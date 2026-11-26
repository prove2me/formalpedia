-- Prove2me | solution 1 for GlobalTheory.basisVal_eq_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:08:50.615384+00:00
-- url     : https://prove2.me/submissions/fa92f7bc-0dbf-43b9-a8dc-22606d34f8bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open Module
variable {R Γ₀ ι κ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
  {O : Type*} [CommRing O] [Algebra O R] [Module O M] [IsScalarTower O R M]

theorem solution (hO : v.Integers O) (c : Basis κ R M)
    (h : Submodule.span O (Set.range b) = Submodule.span O (Set.range c)) (x : M) :
    basisVal v b x = basisVal v c x := by
  have add_le_b (x y : M) :
      basisVal v b (x + y) ≤ max (basisVal v b x) (basisVal v b y) := by
    rw [basisVal_le_iff]
    intro i
    rw [map_add]
    exact (v.map_add _ _).trans (max_le_max
      ((basisVal_le_iff v b).mp le_rfl i)
      ((basisVal_le_iff v b).mp le_rfl i))
  have add_le_c (x y : M) :
      basisVal v c (x + y) ≤ max (basisVal v c x) (basisVal v c y) := by
    rw [basisVal_le_iff]
    intro j
    rw [map_add]
    exact (v.map_add _ _).trans (max_le_max
      ((basisVal_le_iff v c).mp le_rfl j)
      ((basisVal_le_iff v c).mp le_rfl j))
  have le_one_c {y : M} (hy : y ∈ Submodule.span O (Set.range c)) : basisVal v c y ≤ 1 := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      simp [basisVal_basis]
    | zero => simp [basisVal_zero]
    | add x y hx hy ihx ihy => exact (add_le_c x y).trans (max_le ihx ihy)
    | smul r x hx ih =>
      rw [← IsScalarTower.algebraMap_smul (R := O) (A := R) r x, basisVal_smul]
      exact mul_le_one' (hO.map_le_one r) ih
  have le_one_b {y : M} (hy : y ∈ Submodule.span O (Set.range b)) : basisVal v b y ≤ 1 := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      simp [basisVal_basis]
    | zero => simp [basisVal_zero]
    | add x y hx hy ihx ihy => exact (add_le_b x y).trans (max_le ihx ihy)
    | smul r x hx ih =>
      rw [← IsScalarTower.algebraMap_smul (R := O) (A := R) r x, basisVal_smul]
      exact mul_le_one' (hO.map_le_one r) ih
  have hle_bc (i : ι) : basisVal v c (b i) ≤ 1 := by
    apply le_one_c
    rw [← h]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hle_cb (j : κ) : basisVal v b (c j) ≤ 1 := by
    apply le_one_b
    rw [h]
    exact Submodule.subset_span (Set.mem_range_self j)
  refine le_antisymm ?_ ?_
  · rw [basisVal_le_iff]
    intro i
    have : b.repr x i =
        ∑ j ∈ (c.repr x).support, c.repr x j * b.repr (c j) i := by
      conv_lhs => rw [← c.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [this]
    refine v.map_sum_le fun j _ => ?_
    rw [v.map_mul]
    have h1 : v (b.repr (c j) i) ≤ 1 := (basisVal_le_iff v b).mp (hle_cb j) i
    have h2 : v (c.repr x j) ≤ basisVal v c x := (basisVal_le_iff v c).mp le_rfl j
    exact (mul_le_mul' h2 h1).trans_eq (mul_one _)
  · rw [basisVal_le_iff]
    intro j
    have : c.repr x j =
        ∑ i ∈ (b.repr x).support, b.repr x i * c.repr (b i) j := by
      conv_lhs => rw [← b.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [this]
    refine v.map_sum_le fun i _ => ?_
    rw [v.map_mul]
    have h1 : v (c.repr (b i) j) ≤ 1 := (basisVal_le_iff v c).mp (hle_bc i) j
    have h2 : v (b.repr x i) ≤ basisVal v b x := (basisVal_le_iff v b).mp le_rfl i
    exact (mul_le_mul' h2 h1).trans_eq (mul_one _)
