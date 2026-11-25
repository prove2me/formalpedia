-- Prove2me | solution 1 for GroundTheory.Automorphic.IsHilbertSchmidt.isCompactOperator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:31.348813+00:00
-- url     : https://prove2.me/submissions/9bb77f1b-d4e5-4ab7-92d7-56e20ff71d57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Theorems.Thm_GroundTheory_Automorphic_isCompactOperator_hsTruncation
import Theorems.Thm_GroundTheory_Automorphic_hsNormSq_sub_hsTruncation
import Theorems.Thm_GroundTheory_Automorphic_norm_le_hsNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap Filter Topology
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
namespace GroundTheory.Automorphic
namespace IsHilbertSchmidt
theorem _root_.solution {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by
  set b := stdHilbertBasis 𝕜 H
  have htail : Tendsto (fun F : Finset (exists_hilbertBasis 𝕜 H).choose =>
      hsNormSq (T - hsTruncation b T F)) atTop (𝓝 0) := by
    simp only [b, hsNormSq_sub_hsTruncation]
    exact ENNReal.tendsto_tsum_compl_atTop_zero hT.ne
  have hHS : ∀ F, IsHilbertSchmidt (T - hsTruncation b T F) := fun F => by
    refine lt_of_le_of_lt ?_ hT
    rw [hsNormSq_sub_hsTruncation, hsNormSq]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
  have hnorm : Tendsto (fun F => hsNorm (T - hsTruncation b T F)) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail
    have h2 := (Real.continuous_sqrt.tendsto _).comp h1
    simpa [hsNorm, Function.comp_def] using h2
  refine isCompactOperator_of_tendsto (l := atTop) (F := fun F => hsTruncation b T F) ?_
    (Eventually.of_forall fun F => isCompactOperator_hsTruncation b T F)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun F => ?_) hnorm
  rw [norm_sub_rev]
  exact norm_le_hsNorm (hHS F)
end IsHilbertSchmidt
end GroundTheory.Automorphic
