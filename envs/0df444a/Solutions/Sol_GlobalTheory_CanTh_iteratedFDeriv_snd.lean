-- Prove2me | solution 1 for GlobalTheory.CanTh.iteratedFDeriv_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:36.825894+00:00
-- url     : https://prove2.me/submissions/e59431ab-6192-4c2c-8d7b-5f6caef9afd2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMulDotProductLeOfIsCompactThetaDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Theorems.Thm_GlobalTheory_SCV_contDiffOn_nat
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.CanTh
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
namespace GlobalTheory.CanTh
theorem _root_.solution {F : B × W → ℂ} {U : Set (B × W)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {s : B} {x : W} (hx : (s, x) ∈ U) (k : ℕ) (v : Fin k → W) :
    iteratedFDeriv ℂ k (fun w => F (s, w)) x v =
      iteratedFDeriv ℂ k F (s, x) (fun j => (0, v j)) := by
  set L : W →L[ℂ] B × W := ContinuousLinearMap.inr ℂ B W with hL
  set c : B × W := (s, 0) with hc
  set t : Set (B × W) := (fun w => c + w) ⁻¹' U with ht
  have hto : IsOpen t := hU.preimage (by fun_prop)
  have hto' : IsOpen (L ⁻¹' t) := hto.preimage L.continuous
  have hg : DifferentiableOn ℂ (fun w => F (c + w)) t :=
    hF.comp (by fun_prop) fun w hw => hw
  have h0 : L x ∈ t := by simpa [ht, hc, hL] using hx
  have key := L.iteratedFDerivWithin_comp_right (SCV.contDiffOn_nat hto k hg) hto.uniqueDiffOn
    hto'.uniqueDiffOn h0 le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hto' (show x ∈ L ⁻¹' t from h0),
    iteratedFDerivWithin_of_isOpen k hto h0, iteratedFDeriv_comp_add_left] at key
  have e : (fun w => F (s, w)) = (fun w => F (c + w)) ∘ L := by
    ext w
    simp [hL, hc]
  rw [e, key]
  simp [hL, hc]
end GlobalTheory.CanTh
