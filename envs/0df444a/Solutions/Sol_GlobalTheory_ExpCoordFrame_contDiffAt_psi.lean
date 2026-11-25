-- Prove2me | solution 1 for GlobalTheory.ExpCoordFrame.contDiffAt_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:16.118862+00:00
-- url     : https://prove2.me/submissions/cecba902-d7f6-4581-85a6-3ece2ecc0c25

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrame
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
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
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpCoordFrame
open NormedSpace Filter Topology
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {d : ℕ}
local notation "𝔢" => expPartialHomeomorph ℝ 𝔸
namespace GlobalTheory.ExpCoordFrame
theorem _root_.solution (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d)
    (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ (𝔢).source) :
    ContDiffAt ℝ ∞ (Function.uncurry (psi b)) (x, 0) := by
  have hin : exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (((0 : 𝔤)) : 𝔸) ∈ (𝔢).target := by
    have e : exp ((coordEquiv b x : 𝔤) : 𝔸) ∈ (𝔢).target := (𝔢).map_source hx
    simpa using e
  have hlog : ContDiffAt ℝ ∞ (𝔢).symm (exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (((0 : 𝔤)) : 𝔸)) :=
    (contDiffOn_expPartialHomeomorph_symm ℝ 𝔸).contDiffAt ((𝔢).open_target.mem_nhds hin)
  have hm : ContDiff ℝ ∞ (fun p : E d × 𝔤 => exp ((coordEquiv b p.1 : 𝔤) : 𝔸) * exp (p.2 : 𝔸)) :=
    ((contDiff_exp ℝ 𝔸).comp (𝔤.subtypeL.contDiff.comp ((coordEquiv b).contDiff.comp contDiff_fst))).mul
      ((contDiff_exp ℝ 𝔸).comp (𝔤.subtypeL.contDiff.comp contDiff_snd))
  exact (coordEquiv b).symm.contDiff.comp_contDiffAt (x, (0 : 𝔤))
    ((subspaceProj 𝔤).contDiff.comp_contDiffAt (x, (0 : 𝔤)) (hlog.comp (x, (0 : 𝔤)) hm.contDiffAt))
end GlobalTheory.ExpCoordFrame
