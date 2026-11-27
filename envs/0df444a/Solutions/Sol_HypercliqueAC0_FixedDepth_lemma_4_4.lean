-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:03:30.940187+00:00
-- url     : https://prove2.me/submissions/a4c01716-388f-4461-b302-ff555b873cea

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- One-step increment of `F x = x L - C(x,r) q`. -/
lemma L44_step (L q : ℝ) (r : ℕ) (hr : 1 ≤ r) (x : ℕ) :
    (((x + 1 : ℕ) : ℝ) * L - ((x + 1).choose r : ℝ) * q) - ((x : ℝ) * L - (x.choose r : ℝ) * q)
      = L - (x.choose (r - 1) : ℝ) * q := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- `F` is nondecreasing on `{0,…,s}`. -/
lemma L44_mono (L q : ℝ) (hq : 0 ≤ q) (r s : ℕ) (hr : 1 ≤ r)
    (hlog : ((s - 1).choose (r - 1) : ℝ) * q ≤ L) :
    ∀ k a : ℕ, a + k ≤ s →
      (a : ℝ) * L - (a.choose r : ℝ) * q ≤ ((a + k : ℕ) : ℝ) * L - ((a + k).choose r : ℝ) * q := by
  intro k
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a h
    have h1 := ih a (by omega)
    have h2 := L44_step L q r hr (a + k)
    have h3 : ((a + k).choose (r - 1) : ℝ) ≤ ((s - 1).choose (r - 1) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose _ (by omega)
    have h4 : ((a + k).choose (r - 1) : ℝ) * q ≤ ((s - 1).choose (r - 1) : ℝ) * q :=
      mul_le_mul_of_nonneg_right h3 hq
    rw [show a + (k + 1) = a + k + 1 by omega]
    linarith

/-- Increments of `F` are nonincreasing. -/
lemma L44_incr (L q : ℝ) (hq : 0 ≤ q) (r : ℕ) (hr : 1 ≤ r) :
    ∀ j c c' : ℕ, c ≤ c' →
      (((c' + j : ℕ) : ℝ) * L - ((c' + j).choose r : ℝ) * q) - ((c' : ℝ) * L - (c'.choose r : ℝ) * q)
        ≤ (((c + j : ℕ) : ℝ) * L - ((c + j).choose r : ℝ) * q) - ((c : ℝ) * L - (c.choose r : ℝ) * q) := by
  intro j
  induction j with
  | zero => intro c c' _; simp
  | succ j ih =>
    intro c c' h
    have h1 := ih c c' h
    have h2 := L44_step L q r hr (c' + j)
    have h2' := L44_step L q r hr (c + j)
    have h3 : ((c + j).choose (r - 1) : ℝ) ≤ ((c' + j).choose (r - 1) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose _ (by omega)
    have h4 : ((c + j).choose (r - 1) : ℝ) * q ≤ ((c' + j).choose (r - 1) : ℝ) * q :=
      mul_le_mul_of_nonneg_right h3 hq
    rw [show c' + (j + 1) = c' + j + 1 by omega, show c + (j + 1) = c + j + 1 by omega]
    linarith

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (r s : ℕ) (hr : 2 ≤ r) (hs : r ≤ s)
    (Λ p : ℝ) (hΛ : 0 < Λ) (hΛ1 : Λ ≤ 1) (hp : 0 < p) (hp1 : p < 1)
    (hlog : (Nat.choose (s - 1) (r - 1) : ℝ) * Real.log (1 / p) ≤ Real.log (1 / Λ))
    {V : Type*} (P₁ P₂ : Finset V)
    (hP₁ : P₁.card ≤ s) (hP₂ : P₂.card ≤ s) (hunion : s < (P₁ ∪ P₂).card) :
    Λ ^ (P₁ ∪ P₂).card * p ^ (-((P₁.powersetCard r ∪ P₂.powersetCard r).card : ℝ)) ≤
      Λ ^ s * p ^ (-(Nat.choose s r : ℝ)) := by
  set L := Real.log (1 / Λ) with hL
  set q := Real.log (1 / p) with hq
  have hLΛ : Real.log Λ = -L := by rw [hL, one_div, Real.log_inv, neg_neg]
  have hqp : Real.log p = -q := by rw [hq, one_div, Real.log_inv, neg_neg]
  have hq0 : 0 ≤ q := by
    rw [hq]; apply Real.log_nonneg; rw [le_div_iff₀ hp]; linarith
  -- counting
  have hinter : P₁.powersetCard r ∩ P₂.powersetCard r = (P₁ ∩ P₂).powersetCard r := by
    ext x; simp only [Finset.mem_inter, Finset.mem_powersetCard, Finset.subset_inter_iff]
    tauto
  have hE := Finset.card_union_add_card_inter (P₁.powersetCard r) (P₂.powersetCard r)
  rw [hinter, Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_powersetCard] at hE
  have hU := Finset.card_union_add_card_inter P₁ P₂
  set a₁ := P₁.card
  set a₂ := P₂.card
  set c := (P₁ ∩ P₂).card
  set u := (P₁ ∪ P₂).card
  set E := (P₁.powersetCard r ∪ P₂.powersetCard r).card
  have hca : c ≤ a₂ := Finset.card_le_card Finset.inter_subset_right
  have hEr : (E : ℝ) + (c.choose r : ℝ) = (a₁.choose r : ℝ) + (a₂.choose r : ℝ) := by
    exact_mod_cast hE
  have hUr : (u : ℝ) + (c : ℝ) = (a₁ : ℝ) + (a₂ : ℝ) := by exact_mod_cast hU
  -- the combinatorial inequality
  set j := a₂ - c
  set t := s - j
  have htj : t + j = s := by omega
  have hct : c ≤ t := by omega
  have hta : t ≤ a₁ := by omega
  have hr1 : 1 ≤ r := by omega
  have hm := L44_mono L q hq0 r s hr1 hlog (a₁ - t) t (by omega)
  rw [show t + (a₁ - t) = a₁ by omega] at hm
  have hi := L44_incr L q hq0 r hr1 j c t hct
  rw [htj, show c + j = a₂ by omega] at hi
  -- take logs
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_rpow hp, Real.log_rpow hp, hLΛ, hqp]
  have h1 : (u : ℝ) * L = ((a₁ : ℝ) + a₂ - c) * L := by rw [← hUr]; ring
  have h2 : (E : ℝ) * q = ((a₁.choose r : ℝ) + (a₂.choose r : ℝ) - (c.choose r : ℝ)) * q := by
    rw [← hEr]; ring
  linarith

