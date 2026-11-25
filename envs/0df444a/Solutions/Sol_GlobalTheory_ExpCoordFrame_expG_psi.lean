-- Prove2me | solution 1 for GlobalTheory.ExpCoordFrame.expG_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:49:07.823233+00:00
-- url     : https://prove2.me/submissions/5d4323db-c73b-46dd-a469-ddc514b950f8

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
theorem _root_.solution (h : IsExpLieAlgebra G 𝔤) (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d)
    (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    ∀ᶠ Y in 𝓝 (0 : 𝔤), h.expG (coordEquiv b (psi b x Y)) = h.expG (coordEquiv b x) * h.expG Y := by
  have hc : Continuous (fun Y : 𝔤 => exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (Y : 𝔸)) :=
    continuous_const.mul ((contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp continuous_subtype_val)
  have h0 : exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (((0 : 𝔤)) : 𝔸) ∈ h.nhdOne := by
    simpa using h.exp_mem_nhdOne hx
  filter_upwards [hc.continuousAt.preimage_mem_nhds (h.isOpen_nhdOne.mem_nhds h0)] with Y hY
  have hY' : exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (Y : 𝔸) ∈ h.nhdOne := hY
  have hv : (((h.expG (coordEquiv b x) * h.expG Y : G) : 𝔸ˣ) : 𝔸) =
      exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (Y : 𝔸) := by simp
  have hmem := h.symm_mem_lie (x := h.expG (coordEquiv b x) * h.expG Y) (by rw [hv]; exact hY')
  rw [hv] at hmem
  apply Subtype.ext; apply Units.ext
  rw [hv]
  simp only [psi, ContinuousLinearEquiv.apply_symm_apply, IsExpLieAlgebra.coe_expG]
  rw [subspaceProj_of_mem hmem, h.exp_symm hY']
end GlobalTheory.ExpCoordFrame
