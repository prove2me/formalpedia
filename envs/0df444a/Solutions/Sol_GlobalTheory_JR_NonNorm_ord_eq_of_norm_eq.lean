-- Prove2me | solution 1 for GlobalTheory.JR.NonNorm.ord_eq_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:58:33.430016+00:00
-- url     : https://prove2.me/submissions/d132be10-c4d9-40e3-866f-152321bad2e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaKEqNegOneOfNotNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NonNorm
open ValuativeRel GroundTheory.LocalField IntermediateField
namespace GlobalTheory.JR.NonNorm
theorem _root_.solution (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (x y : F) (h : ‖x‖ = ‖y‖) :
    letI := normRel F
    haveI := isLocalField F
    ord x = ord y := by
  letI := normRel F
  haveI := isLocalField F
  have h1 : x ≤ᵥ y := h.le
  have h2 : y ≤ᵥ x := h.ge
  rw [(valuation F).vle_iff_le] at h1 h2
  unfold ord
  rw [normalizedValuation_eq_iff.2 (le_antisymm h1 h2)]
end GlobalTheory.JR.NonNorm
