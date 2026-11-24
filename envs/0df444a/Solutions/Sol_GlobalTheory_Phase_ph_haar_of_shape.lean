-- Prove2me | solution 1 for GlobalTheory.Phase.ph_haar_of_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:40:58.170161+00:00
-- url     : https://prove2.me/submissions/b541befd-26e4-4b12-bd8e-bf178bcd5584

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ComplexPhaseCalculusRootOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralGaussianShapeRootOfUnityPh
import Theorems.Thm_GlobalTheory_Phase_ph_finsum_quotient
import Theorems.Thm_GlobalTheory_Phase_IsMu_mul
import Theorems.Thm_GlobalTheory_Phase_Ph_mul
import Theorems.Thm_GlobalTheory_SW_HaarLevel_finite_support
import Theorems.Thm_GlobalTheory_SW_HaarLevel_periodic
import Theorems.Thm_GlobalTheory_T_complex_phase_calculus_rootOfUnity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase
namespace GlobalTheory.Phase
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Ph (haar φ) := by
  intro κ ι _ _ _ φ hφ
  obtain ⟨hsb, c, a, S, f, hc, hf, hφx⟩ := hφ
  have hR := hsb.choose_spec
  unfold haar
  rw [dif_pos hsb]
  unfold haarAt
  refine Ph.mul ?_ (ph_finsum_quotient (perSub ℚ κ ι hsb.choose) S φ f c a
    (GlobalTheory.SW.HaarLevel.periodic hR.2) (GlobalTheory.SW.HaarLevel.finite_support hR.1 hR.2) hc hf hφx)

  have h := GlobalTheory.T.complex_phase_calculus_rootOfUnity.2.2.1
    (((hsb.choose : ℝ) ^ (Module.finrank ℚ ℚ * (Fintype.card κ * Fintype.card ι)))⁻¹)
  convert h using 1
  push_cast
  rfl
end GlobalTheory.Phase
