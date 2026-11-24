-- Prove2me | solution 1 for HypergraphUnreliability.FPRAS.lemma_9_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:21:54.464126+00:00
-- url     : https://prove2.me/submissions/be835676-de94-4bc0-967b-a5e6c12249a4

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Hypergraph

noncomputable section

open scoped BigOperators Classical

open HypergraphUnreliability.FPRAS HypergraphUnreliability.FPRAS.LabeledHypergraph

namespace ProdProbStability

variable {E : Type} [Fintype E]

/-- Weight of a failed set `t ∌ a` from all coordinates other than `a`. -/
def wt (r : E → ℝ) (a : E) (t : Finset E) : ℝ :=
  (∏ e ∈ t, r e) * ∏ e ∈ tᶜ.erase a, (1 - r e)

/-- Splitting the product law along the coordinate `a`. -/
theorem prodProb_split (r : E → ℝ) (A : Finset E → Prop) (a : E) :
    prodProb r A = ∑ t ∈ (Finset.univ.erase a).powerset,
      ((if A t then (1 - r a) else 0) + (if A (insert a t) then r a else 0)) * wt r a t := by
  unfold prodProb
  have hU : (Finset.univ : Finset E) = insert a (Finset.univ.erase a) :=
    (Finset.insert_erase (Finset.mem_univ a)).symm
  rw [show (Finset.univ : Finset (Finset E)) = (insert a (Finset.univ.erase a)).powerset by
    rw [← hU, Finset.powerset_univ]]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase a _), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hat : a ∉ t := by
    intro h
    exact Finset.notMem_erase a _ (Finset.mem_powerset.mp ht h)
  have h1 : failureMass r t = (1 - r a) * wt r a t := by
    unfold failureMass wt
    rw [← Finset.mul_prod_erase tᶜ (fun e => 1 - r e) (by simpa using hat)]
    ring
  have h2 : failureMass r (insert a t) = r a * wt r a t := by
    unfold failureMass wt
    rw [Finset.prod_insert hat, Finset.compl_insert]
    ring
  rw [h1, h2]
  split_ifs <;> ring

theorem wt_congr (r r' : E → ℝ) (a : E) (hagree : ∀ e, e ≠ a → r' e = r e) (t : Finset E)
    (hat : a ∉ t) : wt r' a t = wt r a t := by
  unfold wt
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    exact hagree e (fun h => hat (h ▸ he))
  · apply Finset.prod_congr rfl
    intro e he
    rw [hagree e (Finset.ne_of_mem_erase he)]

theorem wt_nonneg (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1) (a : E) (t : Finset E) :
    0 ≤ wt r a t := by
  unfold wt
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun e _ => (hr e).1)
  · exact Finset.prod_nonneg (fun e _ => by linarith [(hr e).2])

/-- Changing one coordinate by a factor in `[e^{-τ}, e^{τ}]` changes the probability of an increasing
event by a factor in the same range. -/
theorem one_step (A : Finset E → Prop) (hA : IsIncreasing A) (r r' : E → ℝ)
    (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1) (a : E) (hagree : ∀ e, e ≠ a → r' e = r e)
    (τ : ℝ) (hτ : 0 ≤ τ) (hlo : Real.exp (-τ) * r a ≤ r' a) (hhi : r' a ≤ Real.exp τ * r a) :
    Real.exp (-τ) * prodProb r A ≤ prodProb r' A ∧
      prodProb r' A ≤ Real.exp τ * prodProb r A := by
  have e1 : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have e2 : 1 ≤ Real.exp τ := Real.one_le_exp hτ
  rw [prodProb_split r A a, prodProb_split r' A a, Finset.mul_sum, Finset.mul_sum]
  have hw : ∀ t ∈ (Finset.univ.erase a).powerset, wt r' a t = wt r a t := by
    intro t ht
    apply wt_congr r r' a hagree t
    intro h
    exact Finset.notMem_erase a _ (Finset.mem_powerset.mp ht h)
  constructor
  · apply Finset.sum_le_sum
    intro t ht
    rw [hw t ht]
    have h0 := wt_nonneg r hr a t
    have hmono : A t → A (insert a t) := hA _ _ (Finset.subset_insert a t)
    by_cases h1 : A t
    · rw [if_pos h1, if_pos (hmono h1), if_pos h1, if_pos (hmono h1)]
      nlinarith [mul_le_mul_of_nonneg_right e1 h0]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : A (insert a t)
      · rw [if_pos h2, if_pos h2]
        nlinarith [mul_le_mul_of_nonneg_right hlo h0]
      · rw [if_neg h2, if_neg h2]
        nlinarith
  · apply Finset.sum_le_sum
    intro t ht
    rw [hw t ht]
    have h0 := wt_nonneg r hr a t
    have hmono : A t → A (insert a t) := hA _ _ (Finset.subset_insert a t)
    by_cases h1 : A t
    · rw [if_pos h1, if_pos (hmono h1), if_pos h1, if_pos (hmono h1)]
      nlinarith [mul_le_mul_of_nonneg_right e2 h0]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : A (insert a t)
      · rw [if_pos h2, if_pos h2]
        nlinarith [mul_le_mul_of_nonneg_right hhi h0]
      · rw [if_neg h2, if_neg h2]
        nlinarith

/-- The hybrid law using `q` on `s` and `p` elsewhere. -/
def mix (p q : E → ℝ) (s : Finset E) : E → ℝ := fun e => if e ∈ s then q e else p e

theorem hybrid (A : Finset E → Prop) (hA : IsIncreasing A) (p q t : E → ℝ)
    (hp : ∀ e, p e ∈ Set.Icc (0 : ℝ) 1) (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    (ht : ∀ e, 0 ≤ t e)
    (hlow : ∀ e, Real.exp (-t e) * p e ≤ q e) (hupp : ∀ e, q e ≤ Real.exp (t e) * p e)
    (s : Finset E) :
    Real.exp (-∑ e ∈ s, t e) * prodProb p A ≤ prodProb (mix p q s) A ∧
      prodProb (mix p q s) A ≤ Real.exp (∑ e ∈ s, t e) * prodProb p A := by
  induction s using Finset.induction_on with
  | empty =>
    have : mix p q ∅ = p := by funext e; simp [mix]
    simp [this]
  | insert a s has ih =>
    have hmix : ∀ e, mix p q s e ∈ Set.Icc (0 : ℝ) 1 := by
      intro e; unfold mix; split_ifs
      · exact hq e
      · exact hp e
    have hagree : ∀ e, e ≠ a → mix p q (insert a s) e = mix p q s e := by
      intro e he; simp [mix, Finset.mem_insert, he]
    have hA1 : mix p q (insert a s) a = q a := by simp [mix]
    have hA2 : mix p q s a = p a := by simp [mix, has]
    obtain ⟨s1, s2⟩ := one_step A hA (mix p q s) (mix p q (insert a s)) hmix a hagree (t a) (ht a)
      (by rw [hA1, hA2]; exact hlow a) (by rw [hA1, hA2]; exact hupp a)
    rw [Finset.sum_insert has]
    obtain ⟨i1, i2⟩ := ih
    have ea : 0 < Real.exp (-t a) := Real.exp_pos _
    have eb : 0 < Real.exp (t a) := Real.exp_pos _
    constructor
    · rw [neg_add, Real.exp_add, mul_assoc]
      exact (mul_le_mul_of_nonneg_left i1 ea.le).trans s1
    · rw [Real.exp_add, mul_assoc]
      exact s2.trans (mul_le_mul_of_nonneg_left i2 eb.le)

end ProdProbStability

open ProdProbStability in
theorem solution {E : Type} [Fintype E] (A : Finset E → Prop) (hA : IsIncreasing A)
    (p q t : E → ℝ) (hp : ∀ e, p e ∈ Set.Icc (0 : ℝ) 1) (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    (ht : ∀ e, 0 ≤ t e)
    (hlow : ∀ e, Real.exp (-t e) * p e ≤ q e) (hupp : ∀ e, q e ≤ Real.exp (t e) * p e) :
    Real.exp (-∑ e, t e) * prodProb p A ≤ prodProb q A ∧
      prodProb q A ≤ Real.exp (∑ e, t e) * prodProb p A := by
  have hq' : mix p q Finset.univ = q := by funext e; simp [mix]
  have := hybrid A hA p q t hp hq ht hlow hupp Finset.univ
  rw [hq'] at this
  exact this
