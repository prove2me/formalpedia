-- Prove2me | solution 1 for GroundTheory.Automorphic.analyticAt_expPartialHomeomorph_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:13.224685+00:00
-- url     : https://prove2.me/submissions/a6b45210-b7cc-4923-ad29-d2aac88e9894

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
namespace GroundTheory.Automorphic
theorem _root_.solution {y : 𝔸}
    (hy : y ∈ (expPartialHomeomorph ℝ 𝔸).target) :
    AnalyticAt ℝ (expPartialHomeomorph ℝ 𝔸).symm y := by
  set e := expPartialHomeomorph ℝ 𝔸 with he
  have hs : e.symm y ∈ e.source := e.map_target hy
  have hu : IsUnit (fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y)) :=
    expPartialHomeomorph_source_subset ℝ 𝔸 hs
  obtain ⟨p, hp⟩ := exp_analytic (𝕂 := ℝ) (e.symm y)
  have hp' : HasFPowerSeriesAt e p (e.symm y) := by
    rw [he, coe_expPartialHomeomorph]; exact hp
  have h1 : p 1 = (continuousMultilinearCurryFin1 ℝ 𝔸 𝔸).symm
      ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) := by
    have h2 := hp.fderiv_eq
    have h3 : ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) =
        fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y) := by
      ext x; simp
    rw [h3, h2, LinearIsometryEquiv.symm_apply_apply]
  have := e.hasFPowerSeriesAt_symm hs hp' h1
  rw [e.right_inv hy] at this
  exact this.analyticAt
end GroundTheory.Automorphic
