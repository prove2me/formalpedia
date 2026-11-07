-- Prove2me | solution 1 for HordijkKallenbergLP.ExtremePoint.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:35:10.181447+00:00
-- url     : https://prove2.me/submissions/aca08846-cd4e-40bb-b662-8fe9fa01e169

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_ExtremePoint_Model
import Theorems.Thm_HordijkKallenbergLP_ExtremePoint_representative_feasible
import Theorems.Thm_HordijkKallenbergLP_ExtremePoint_system7_solution
import Theorems.Thm_HordijkKallenbergLP_ExtremePoint_system7_transient
import Theorems.Thm_HordijkKallenbergLP_ExtremePoint_repY_zero_on_ergodic
import Theorems.Thm_HordijkKallenbergLP_ExtremePoint_invariant_vanishes_on_ergodic
open Matrix MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace HordijkKallenbergLP.ExtremePoint.Glue

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma policyMatrix_markov (M : StationaryMDP S A) (π : S → A → ℝ) (hπ : IsStationaryRule M π) :
    IsMarkovMatrix (policyMatrix M π) := by
  refine ⟨fun i j => Finset.sum_nonneg fun a ha => mul_nonneg (M.trans_nonneg i a j)
    (hπ.1 i a ha), fun i => ?_⟩
  unfold policyMatrix
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, M.trans_sum, one_mul]
  exact hπ.2 i

lemma pure_isRule (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) :
    IsStationaryRule M (pureRule f) := by
  refine ⟨fun i a _ => ?_, fun i => ?_⟩
  · unfold pureRule; split_ifs <;> norm_num
  · simp [pureRule, hf i]

lemma policy_pure (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (i j : S) : policyMatrix M (pureRule f) i j = M.trans i (f i) j := by
  simp [policyMatrix, pureRule, hf i]

lemma mem_ergodicSet_iff (P : Matrix S S ℝ) (l i : S) :
    i ∈ ergodicSet P l ↔ Accessible P l i := by
  classical
  simp [ergodicSet]

/-- The selected pair `(i, f(i))`. -/
def sel (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (i : S) : Pair M :=
  ⟨(i, f i), hf i⟩

lemma sel_of (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (p : Pair M) (hp : p.1.2 = f p.1.1) : sel M f hf p.1.1 = p := by
  apply Subtype.ext
  change (p.1.1, f p.1.1) = p.1
  rw [← hp]

/-- A sum over admissible pairs of a vector supported on the selected pairs. -/
lemma sum_sel (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (w G : Pair M → ℝ) (hw : ∀ p : Pair M, p.1.2 ≠ f p.1.1 → w p = 0) :
    ∑ p : Pair M, G p * w p = ∑ i, G (sel M f hf i) * w (sel M f hf i) := by
  symm
  apply Fintype.sum_of_injective (sel M f hf)
  · intro i j h; exact congrArg (fun p : Pair M => p.1.1) h
  · intro p hp
    have : p.1.2 ≠ f p.1.1 := fun h => hp ⟨p.1.1, sel_of M f hf p h⟩
    rw [hw p this, mul_zero]
  · intro i; rfl

lemma pos_comb_zero {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : a * u + b * v = 0) : u = 0 ∧ v = 0 := by
  have h1 : a * u = 0 := by nlinarith [mul_nonneg ha.le hu, mul_nonneg hb.le hv]
  have h2 : b * v = 0 := by nlinarith [mul_nonneg ha.le hu, mul_nonneg hb.le hv]
  exact ⟨(mul_eq_zero.1 h1).resolve_left ha.ne', (mul_eq_zero.1 h2).resolve_left hb.ne'⟩

/-- A feasible point supported on the selected pairs solves system (7). -/
lemma feasible_system7 (M : StationaryMDP S A) (β : S → ℝ) (f : S → A)
    (hf : ∀ i, f i ∈ M.admissible i) (z : (Pair M → ℝ) × (Pair M → ℝ))
    (hz : z ∈ dualFeasible M β)
    (h1 : ∀ p : Pair M, p.1.2 ≠ f p.1.1 → z.1 p = 0)
    (h2 : ∀ p : Pair M, p.1.2 ≠ f p.1.1 → z.2 p = 0) :
    (fun i => z.1 (sel M f hf i)) ᵥ* (1 - policyMatrix M (pureRule f)) = 0 ∧
    (fun i => z.1 (sel M f hf i)) +
      (fun i => z.2 (sel M f hf i)) ᵥ* (1 - policyMatrix M (pureRule f)) = β := by
  obtain ⟨hz3, hz4, -, -⟩ := hz
  have hv : ∀ (w : S → ℝ) (j : S), (w ᵥ* (1 - policyMatrix M (pureRule f))) j =
      ∑ i, ((if i = j then (1 : ℝ) else 0) - M.trans i (f i) j) * w i := by
    intro w j
    simp only [Matrix.vecMul, dotProduct, Matrix.sub_apply, Matrix.one_apply, policy_pure M f hf]
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor
  · funext j
    have h := hz3 j
    rw [sum_sel M f hf z.1 _ h1] at h
    rw [hv, Pi.zero_apply]
    exact h
  · funext j
    have h := hz4 j
    have e : (∑ p : Pair M, if p.1.1 = j then z.1 p else 0) =
        ∑ p : Pair M, (if p.1.1 = j then (1 : ℝ) else 0) * z.1 p :=
      Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
    rw [e, sum_sel M f hf z.1 _ h1, sum_sel M f hf z.2 _ h2] at h
    rw [Pi.add_apply, hv, ← h]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp [sel]
    · intro i _ hij; simp [sel, hij]
    · intro h; exact absurd (Finset.mem_univ j) h

end HordijkKallenbergLP.ExtremePoint.Glue

open HordijkKallenbergLP.ExtremePoint HordijkKallenbergLP.ExtremePoint.Glue in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) :
    (repX M β (pureRule f), repY M β (pureRule f)) ∈
      Set.extremePoints ℝ (dualFeasible M β) := by
  set P := policyMatrix M (pureRule f) with hPdef
  have hP : IsMarkovMatrix P := policyMatrix_markov M _ (pure_isRule M f hf)
  have hfeas := representative_feasible M β hβpos hβsum (pureRule f) (pure_isRule M f hf)
  rw [mem_extremePoints]
  refine ⟨hfeas, ?_⟩
  rintro ⟨x1, y1⟩ hz1 ⟨x2, y2⟩ hz2 ⟨a, b, ha, hb, hab, hcomb⟩
  have hX : ∀ p, a * x1 p + b * x2 p = repX M β (pureRule f) p := by
    intro p; have := congrFun (congrArg Prod.fst hcomb) p; simpa using this
  have hY : ∀ p, a * y1 p + b * y2 p = repY M β (pureRule f) p := by
    intro p; have := congrFun (congrArg Prod.snd hcomb) p; simpa using this
  have hoff : ∀ p : Pair M, p.1.2 ≠ f p.1.1 →
      x1 p = 0 ∧ x2 p = 0 ∧ y1 p = 0 ∧ y2 p = 0 := by
    intro p hp
    have hpr : pureRule f p.1.1 p.1.2 = 0 := by simp [pureRule, hp]
    have e1 : a * x1 p + b * x2 p = 0 := by
      rw [hX p]; change _ * pureRule f p.1.1 p.1.2 = 0; rw [hpr, mul_zero]
    have e2 : a * y1 p + b * y2 p = 0 := by
      rw [hY p]; change _ * pureRule f p.1.1 p.1.2 = 0; rw [hpr, mul_zero]
    obtain ⟨u1, u2⟩ := pos_comb_zero ha hb (hz1.2.2.1 p) (hz2.2.2.1 p) e1
    obtain ⟨v1, v2⟩ := pos_comb_zero ha hb (hz1.2.2.2 p) (hz2.2.2.2 p) e2
    exact ⟨u1, u2, v1, v2⟩
  obtain ⟨s1a, s1b⟩ := feasible_system7 M β f hf (x1, y1) hz1
    (fun p hp => (hoff p hp).1) (fun p hp => (hoff p hp).2.2.1)
  obtain ⟨s2a, s2b⟩ := feasible_system7 M β f hf (x2, y2) hz2
    (fun p hp => (hoff p hp).2.1) (fun p hp => (hoff p hp).2.2.2)
  set xb1 : S → ℝ := fun i => x1 (sel M f hf i)
  set xb2 : S → ℝ := fun i => x2 (sel M f hf i)
  set yb1 : S → ℝ := fun i => y1 (sel M f hf i)
  set yb2 : S → ℝ := fun i => y2 (sel M f hf i)
  have hx1 := (system7_solution P hP β xb1 yb1 s1a s1b).1
  have hx2 := (system7_solution P hP β xb2 yb2 s2a s2b).1
  -- the difference of the y-parts
  set w : S → ℝ := yb1 - yb2 with hw
  have hwP : w ᵥ* (1 - P) = 0 := by
    have : xb1 + yb1 ᵥ* (1 - P) - (xb2 + yb2 ᵥ* (1 - P)) = 0 := by rw [s1b, s2b, sub_self]
    rw [hx1, hx2, add_sub_add_left_eq_sub, ← Matrix.sub_vecMul] at this
    exact this
  have hwfix : ∀ i, w i = ∑ k, w k * P k i := by
    intro i
    have := congrFun hwP i
    simp only [Matrix.vecMul, dotProduct, Matrix.sub_apply, Matrix.one_apply, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Pi.zero_apply] at this
    linarith
  have htr : ∀ i, ¬ IsRecurrent P i → w i = 0 := by
    intro i hi
    have e1 := system7_transient P hP β xb1 yb1 s1a s1b i hi
    have e2 := system7_transient P hP β xb2 yb2 s2a s2b i hi
    simp only [hw, Pi.sub_apply, e1, e2, sub_self]
  have hw0 : ∀ i, w i = 0 := by
    intro i
    by_cases hi : IsRecurrent P i
    · have hzC : ∀ i' ∈ ergodicSet P i, w i' = ∑ k ∈ ergodicSet P i, w k * P k i' := by
        intro i' hi'
        rw [hwfix i']
        refine (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => ?_)).symm
        by_cases hpk : P k i' = 0
        · rw [hpk, mul_zero]
        · have hpos : 0 < P k i' := lt_of_le_of_ne (hP.1 k i') (Ne.symm hpk)
          by_cases hkr : IsRecurrent P k
          · exfalso
            have hik : Accessible P i k :=
              ((mem_ergodicSet_iff P i i').1 hi').trans
                (hkr i' (Relation.ReflTransGen.single hpos))
            exact hk ((mem_ergodicSet_iff P i k).2 hik)
          · rw [htr k hkr, zero_mul]
      obtain ⟨i0, hi0, hy0⟩ := repY_zero_on_ergodic M β hβpos hβsum f hf i hi
      have e : a * y1 (sel M f hf i0) + b * y2 (sel M f hf i0) = 0 := by
        rw [hY]; exact hy0
      obtain ⟨u1, u2⟩ := pos_comb_zero ha hb (hz1.2.2.2 _) (hz2.2.2.2 _) e
      have u1' : y1 (sel M f hf i0) = 0 := u1
      have u2' : y2 (sel M f hf i0) = 0 := u2
      have hwi0 : w i0 = 0 := by
        show y1 (sel M f hf i0) - y2 (sel M f hf i0) = 0
        rw [u1', u2', sub_self]
      exact invariant_vanishes_on_ergodic P hP i hi w hzC i0 hi0 hwi0 i
        (mem_ergodicSet_self P i)
    · exact htr i hi
  have hyeq : ∀ i, yb1 i = yb2 i := fun i => sub_eq_zero.1 (hw0 i)
  have hxeq : ∀ i, xb1 i = xb2 i := fun i => by rw [hx1, hx2]
  -- conclude
  have key1 : ∀ p, x1 p = repX M β (pureRule f) p ∧ x2 p = repX M β (pureRule f) p := by
    intro p
    by_cases hp : p.1.2 = f p.1.1
    · have hs := sel_of M f hf p hp
      have e := hxeq p.1.1
      simp only [xb1, xb2, hs] at e
      rw [← hX p, e]
      constructor <;> linear_combination -(x2 p) * hab
    · obtain ⟨u1, u2, -, -⟩ := hoff p hp
      rw [← hX p, u1, u2]; simp
  have key2 : ∀ p, y1 p = repY M β (pureRule f) p ∧ y2 p = repY M β (pureRule f) p := by
    intro p
    by_cases hp : p.1.2 = f p.1.1
    · have hs := sel_of M f hf p hp
      have e := hyeq p.1.1
      simp only [yb1, yb2, hs] at e
      rw [← hY p, e]
      constructor <;> linear_combination -(y2 p) * hab
    · obtain ⟨-, -, u1, u2⟩ := hoff p hp
      rw [← hY p, u1, u2]; simp
  refine ⟨Prod.ext (funext fun p => (key1 p).1) (funext fun p => (key2 p).1),
    Prod.ext (funext fun p => (key1 p).2) (funext fun p => (key2 p).2)⟩
