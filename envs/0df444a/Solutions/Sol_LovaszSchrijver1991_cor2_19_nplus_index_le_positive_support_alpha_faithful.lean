-- Prove2me | solution 1 for LovaszSchrijver1991.cor2_19_nplus_index_le_positive_support_alpha_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:26:45.969664+00:00
-- url     : https://prove2.me/submissions/392c7ee4-38ed-4e63-9252-ec888f7e5673

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet
import Theorems.Thm_LovaszSchrijver_NPlus_nplusIndex_le_succ

open LovaszSchrijver.NPlus

namespace LS87

variable {V : Type} [Fintype V] [DecidableEq V]

lemma sum_chi (a : V → ℝ) (A : Finset V) : ∑ i, a i * chi A i = ∑ i ∈ A, a i := by
  simp [chi, mul_ite, Finset.sum_ite_mem]

lemma valid_of_gen (G : SimpleGraph V) (a : V → ℝ) (b : ℝ)
    (h : ∀ A : Finset V, G.IsIndepSet (A : Set V) → ∑ i ∈ A, a i ≤ b) :
    Valid (STAB G) a b := by
  intro x hx
  have hconv : Convex ℝ {x : V → ℝ | ∑ i, a i * x i ≤ b} := by
    have : {x : V → ℝ | ∑ i, a i * x i ≤ b} =
        (fun x : V → ℝ => ∑ i, a i * x i) ⁻¹' Set.Iic b := rfl
    rw [this]
    refine (convex_Iic b).linear_preimage
      { toFun := fun x : V → ℝ => ∑ i, a i * x i
        map_add' := ?_, map_smul' := ?_ }
    · intro x y; simp [mul_add, Finset.sum_add_distrib]
    · intro c x; simp [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  refine (convexHull_min ?_ hconv) hx
  rintro _ ⟨A, hA, rfl⟩
  show ∑ i, a i * chi A i ≤ b
  rw [sum_chi]; exact h A hA

end LS87

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (b : ℝ) (r : ℕ)
    (hvalid : Valid (STAB G) a b)
    (hα : ∀ A : Finset V, G.IsIndepSet (A : Set V) → (A : Set V) ⊆ {i | 0 < a i} → A.card ≤ r) :
    Valid (NplusG r G) a b := by
  classical
  induction r generalizing a b with
  | zero =>
    have hb : 0 ≤ b := by
      have h0 : chi (∅ : Finset V) ∈ STAB G :=
        subset_convexHull ℝ _ ⟨∅, by simp, rfl⟩
      have := hvalid _ h0
      simpa [chi] using this
    have ha : ∀ i, a i ≤ 0 := by
      intro i
      by_contra hi
      push Not at hi
      have := hα {i} (by simp) (by simpa using hi)
      simp at this
    intro x hx
    have hx0 : ∀ i, 0 ≤ x i := fun i => hx.1 i
    calc ∑ i, a i * x i ≤ ∑ i : V, (0 : ℝ) :=
          Finset.sum_le_sum fun i _ => mul_nonpos_of_nonpos_of_nonneg (ha i) (hx0 i)
      _ = 0 := by simp
      _ ≤ b := hb
  | succ r ih =>
    apply nplusIndex_le_succ G hG a b hvalid r
    intro v hv
    apply ih
    · -- contraction is valid for STAB
      apply LS87.valid_of_gen
      intro A hA
      set A' := A.filter (fun w => ¬ (w = v ∨ G.Adj v w)) with hA'
      have hsum : ∑ i ∈ A, contractCoeff G a v i = ∑ i ∈ A', a i := by
        rw [hA', Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [contractCoeff]
        split_ifs <;> simp_all
      have hvA' : v ∉ A' := by simp [hA']
      have hind : G.IsIndepSet ((insert v A' : Finset V) : Set V) := by
        intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hA',
          Finset.mem_filter] at hx hy
        rcases hx with rfl | ⟨hxA, hxn⟩ <;> rcases hy with rfl | ⟨hyA, hyn⟩
        · exact absurd rfl hxy
        · intro hadj; exact hyn (Or.inr hadj)
        · intro hadj; exact hxn (Or.inr hadj.symm)
        · exact hA hxA hyA hxy
      have h1 := hvalid _ (subset_convexHull ℝ _ ⟨_, hind, rfl⟩)
      rw [LS87.sum_chi, Finset.sum_insert hvA'] at h1
      rw [hsum]; linarith
    · -- positive support of the contraction has smaller independence number
      intro A hA hpos
      have hAv : ∀ w ∈ A, ¬ (w = v ∨ G.Adj v w) := by
        intro w hw hc
        have := hpos hw
        simp only [Set.mem_ofPred_eq, contractCoeff, if_pos hc] at this
        exact lt_irrefl _ this
      have hvA : v ∉ A := fun h => hAv v h (Or.inl rfl)
      have hind : G.IsIndepSet ((insert v A : Finset V) : Set V) := by
        intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
        rcases hx with rfl | hxA <;> rcases hy with rfl | hyA
        · exact absurd rfl hxy
        · intro hadj; exact hAv y hyA (Or.inr hadj)
        · intro hadj; exact hAv x hxA (Or.inr hadj.symm)
        · exact hA hxA hyA hxy
      have hsub : ((insert v A : Finset V) : Set V) ⊆ {i | 0 < a i} := by
        intro w hw
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hw
        rcases hw with rfl | hwA
        · exact hv
        · have := hpos hwA
          simp only [Set.mem_ofPred_eq, contractCoeff, if_neg (hAv w hwA)] at this
          exact this
      have := hα _ hind hsub
      rw [Finset.card_insert_of_notMem hvA] at this
      omega
