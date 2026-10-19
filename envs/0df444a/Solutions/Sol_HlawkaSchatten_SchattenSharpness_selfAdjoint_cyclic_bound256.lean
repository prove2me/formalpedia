-- Prove2me | solution 1 for HlawkaSchatten.SchattenSharpness.selfAdjoint_cyclic_bound256
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-16T23:56:43.79492+00:00
-- url     : https://prove2.me/submissions/d4be9293-2df9-4ef5-be5d-0850cf4a9ae8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HlawkaSchatten_SchattenNorm
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Theorems.Thm_HlawkaSchatten_SchattenSharpness_realSymmetric_cyclic_bound256
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Data.Multiset.Fintype

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

universe u

noncomputable section

namespace HlawkaSchatten.Realification

theorem powerSum_eq_eigenvalue_sum
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (p : ℝ) (hp : p ≠ 0) (T : E →ₗ[𝕜] E) :
    singularValuePowerSum p T =
      ∑ index : Fin (Module.finrank 𝕜 E),
        (Real.sqrt (T.isSymmetric_adjoint_comp_self.eigenvalues rfl index)) ^ p := by
  classical
  have rank_le := T.finrank_range_le
  have extend_sum :
      (∑ index ∈ Finset.range (Module.finrank 𝕜 T.range), T.singularValues index ^ p) =
        ∑ index ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues index ^ p := by
    apply Finset.sum_subset (Finset.range_mono rank_le)
    intro index _ outside
    have rank_le_index : Module.finrank 𝕜 T.range ≤ index :=
      Nat.le_of_not_gt (fun inside => outside (Finset.mem_range.mpr inside))
    rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr rank_le_index,
      Real.zero_rpow hp]
  unfold singularValuePowerSum
  rw [T.support_singularValues, extend_sum,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro index _
  rw [T.singularValues_fin rfl index]

theorem count_eigenvalue_list {Index : Type*} [Fintype Index]
    (values : Index → ℝ) (value : ℝ) :
    (Finset.univ.val.map values).count value =
      (Finset.univ.filter fun index => values index = value).card := by
  classical
  simp only [Multiset.count_map, ← Finset.filter_val, Finset.card, eq_comm]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]

local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

omit [FiniteDimensional ℂ H] in
theorem eigenspace_restrictScalars (T : H →ₗ[ℂ] H) (value : ℝ) :
    Module.End.eigenspace (T.restrictScalars ℝ) value =
      (Module.End.eigenspace T (value : ℂ)).restrictScalars ℝ := by
  ext vector
  simp only [Submodule.restrictScalars_mem, Module.End.mem_eigenspace_iff,
    LinearMap.restrictScalars_apply, Complex.coe_smul]

theorem eigenvalue_list_restrictScalars (T : H →ₗ[ℂ] H) (symmetric : T.IsSymmetric) :
    Finset.univ.val.map (symmetric.restrictScalars.eigenvalues rfl) =
      Finset.univ.val.map (symmetric.eigenvalues rfl) +
        Finset.univ.val.map (symmetric.eigenvalues rfl) := by
  classical
  apply Multiset.ext.mpr
  intro value
  rw [Multiset.count_add]
  simp only [count_eigenvalue_list]
  have complex_count :
      (Finset.univ.filter fun index => symmetric.eigenvalues rfl index = value).card =
        Module.finrank ℂ (Module.End.eigenspace T (value : ℂ)) := by
    have counts := symmetric.card_filter_eigenvalues_eq rfl (value : ℂ)
    convert counts using 1
    congr 1
    ext index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (symmetric.eigenvalues rfl index = value) ↔
      (RCLike.ofReal (symmetric.eigenvalues rfl index) : ℂ) = RCLike.ofReal value
    exact (RCLike.ofReal_inj (K := ℂ)).symm
  have real_count := symmetric.restrictScalars.card_filter_eigenvalues_eq rfl value
  simp only [RCLike.ofReal_real_eq_id, id_eq] at real_count
  rw [real_count, complex_count, eigenspace_restrictScalars]
  change Module.finrank ℝ (Module.End.eigenspace T (value : ℂ)) =
    Module.finrank ℂ (Module.End.eigenspace T (value : ℂ)) +
      Module.finrank ℂ (Module.End.eigenspace T (value : ℂ))
  rw [finrank_real_of_complex]
  omega

theorem eigenvalue_sum_restrictScalars (T : H →ₗ[ℂ] H) (symmetric : T.IsSymmetric)
    (function : ℝ → ℝ) :
    (∑ index, function (symmetric.restrictScalars.eigenvalues rfl index)) =
      2 * ∑ index, function (symmetric.eigenvalues rfl index) := by
  have lists := eigenvalue_list_restrictScalars T symmetric
  have sums := congrArg (fun values : Multiset ℝ => (values.map function).sum) lists
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map] at sums
  change (∑ index, function (symmetric.restrictScalars.eigenvalues rfl index)) =
      (∑ index, function (symmetric.eigenvalues rfl index)) +
        ∑ index, function (symmetric.eigenvalues rfl index) at sums
  linarith

theorem adjoint_restrictScalars (T : H →ₗ[ℂ] H) :
    T.adjoint.restrictScalars ℝ = (T.restrictScalars ℝ).adjoint := by
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro first second
  simp only [LinearMap.restrictScalars_apply, real_inner_eq_re_inner,
    LinearMap.adjoint_inner_left]

theorem powerSum_restrictScalars (p : ℝ) (hp : p ≠ 0) (T : H →ₗ[ℂ] H) :
    singularValuePowerSum p (T.restrictScalars ℝ) = 2 * singularValuePowerSum p T := by
  rw [powerSum_eq_eigenvalue_sum p hp, powerSum_eq_eigenvalue_sum p hp]
  have transfer := eigenvalue_sum_restrictScalars (T.adjoint.comp T)
    T.isSymmetric_adjoint_comp_self (fun value => (Real.sqrt value) ^ p)
  simpa only [LinearMap.restrictScalars_comp, adjoint_restrictScalars] using transfer

theorem schattenPNorm_restrictScalars (p : ℝ) (hp : p ≠ 0) (T : H →ₗ[ℂ] H) :
    schattenPNorm p (T.restrictScalars ℝ) = 2 ^ (1 / p) * schattenPNorm p T := by
  unfold schattenPNorm
  rw [powerSum_restrictScalars p hp]
  exact Real.mul_rpow (by norm_num) (singularValuePowerSum_nonneg p T)

end HlawkaSchatten.Realification

theorem HlawkaSchatten.Realification.selfAdjoint_of_realSymmetric
    (p : ℝ) (hp : 256 ≤ p)
    (real_bound : ∀ (Space : Type u)
      [NormedAddCommGroup Space] [InnerProductSpace ℝ Space] [FiniteDimensional ℝ Space]
      (first second third : Space →ₗ[ℝ] Space),
      first.IsSymmetric → second.IsSymmetric → third.IsSymmetric →
      tripleGap (schattenPNorm p : (Space →ₗ[ℝ] Space) → ℝ) first second third ≤
        cyclicConstant p *
          pairGapSum (schattenPNorm p : (Space →ₗ[ℝ] Space) → ℝ) first second third)
    (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A B C : H →ₗ[ℂ] H)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hC : C.IsSymmetric) :
    tripleGap (schattenPNorm p : (H →ₗ[ℂ] H) → ℝ) A B C ≤
      cyclicConstant p * pairGapSum (schattenPNorm p : (H →ₗ[ℂ] H) → ℝ) A B C := by
  let _ : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have nonzero : p ≠ 0 := by linarith
  have factor_positive : 0 < (2 : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos (by norm_num) _
  have real_inequality := real_bound H
    (A.restrictScalars ℝ) (B.restrictScalars ℝ) (C.restrictScalars ℝ)
    hA.restrictScalars hB.restrictScalars hC.restrictScalars
  simp only [tripleGap, pairGapSum, pairGap, ← LinearMap.restrictScalars_add,
    HlawkaSchatten.Realification.schattenPNorm_restrictScalars p nonzero] at real_inequality
  unfold tripleGap pairGapSum pairGap
  apply le_of_mul_le_mul_left (a := (2 : ℝ) ^ (1 / p)) ?_ factor_positive
  convert real_inequality using 1 <;> first | rfl | ring

end

theorem solution
    (p : ℝ) (hp : 256 ≤ p)
    (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A B C : H →ₗ[ℂ] H)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hC : C.IsSymmetric) :
    tripleGap (schattenPNorm p : (H →ₗ[ℂ] H) → ℝ) A B C ≤
      cyclicConstant p * pairGapSum (schattenPNorm p : (H →ₗ[ℂ] H) → ℝ) A B C := by
  exact HlawkaSchatten.Realification.selfAdjoint_of_realSymmetric p hp
    (HlawkaSchatten.SchattenSharpness.realSymmetric_cyclic_bound256 p hp)
    H A B C hA hB hC
