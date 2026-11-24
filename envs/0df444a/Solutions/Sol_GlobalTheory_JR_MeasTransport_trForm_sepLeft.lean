-- Prove2me | solution 1 for GlobalTheory.JR.MeasTransport.trForm_sepLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:19.097003+00:00
-- url     : https://prove2.me/submissions/cd53113c-fd4a-4f33-9913-7e85da0634c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapIsIsomSelfDualMeasureKerLEqPiHaar
import Theorems.Thm_GlobalTheory_JR_MeasTransport_trForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MeasTransport
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.MeasTransport
theorem _root_.solution [hU : Unram F E] (r : ℕ) (c : Fin r → E) (h : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  haveI : CharZero F := hU.charZero
  by_contra hc
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hc (funext h')
  have h1 := h (Pi.single i (star (c i))⁻¹)
  rw [trForm_apply, dotProduct_single, Pi.star_apply, mul_inv_cancel₀ (star_ne_zero.mpr hi),
    ← map_one (algebraMap F E), Algebra.trace_algebraMap, hU.finrank_eq] at h1
  norm_num at h1
end GlobalTheory.JR.MeasTransport
