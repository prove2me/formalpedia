-- Prove2me | solution 1 for OAI.MatchingSmoothing.trace_square_compression_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:14:13.116306+00:00
-- url     : https://prove2.me/submissions/911a9b7d-3017-4eec-a7cb-bcd820bedfc1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/SpectralContraction.lean:L36-L65
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.trace_square_compression_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction

-- ---- from OAI.Combinatorics.MatchingPSD.SpectralContraction ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
open scoped RealInnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma compression_symmetric (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (W : Submodule ℝ E) : (compression A W).IsSymmetric := by
  intro x y
  change ⟪W.orthogonalProjectionOnto (A x), y⟫ =
    ⟪x, W.orthogonalProjectionOnto (A y)⟫
  simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using hA x y

omit [FiniteDimensional ℝ E] in
lemma trace_square_eq_sum_norm_sq (A : Module.End ℝ E) (hA : A.IsSymmetric)
    {ι : Type u_2} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    LinearMap.trace ℝ E (A * A) = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, ← hA, real_inner_self_eq_norm_sq]

lemma trace_square_compression_le (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (W : Submodule ℝ E) :
    LinearMap.trace ℝ W (compression A W * compression A W) ≤
      LinearMap.trace ℝ E (A * A) := by
  classical
  let b := stdOrthonormalBasis ℝ W
  let e := stdOrthonormalBasis ℝ E
  rw [trace_square_eq_sum_norm_sq _ (compression_symmetric A hA W) b,
    trace_square_eq_sum_norm_sq A hA e]
  calc
    ∑ i, ‖compression A W (b i)‖ ^ 2 ≤ ∑ i, ‖A (b i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr
        (W.norm_orthogonalProjectionOnto_apply_le _)
    _ = ∑ i, ∑ j, ⟪e j, A (b i)⟫ ^ 2 := by
      simp_rw [e.sum_sq_inner_right]
    _ = ∑ j, ∑ i, ⟪(b i : E), A (e j)⟫ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [← hA, real_inner_comm]
    _ ≤ ∑ j, ‖A (e j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hb := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
      have hh := hb.sum_inner_products_le (A (e j)) (s := Finset.univ)
      simpa only [Function.comp_apply, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, Real.norm_eq_abs, sq_abs] using hh

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.trace_square_compression_le := @_root_.OAI.MatchingSmoothing.trace_square_compression_le
