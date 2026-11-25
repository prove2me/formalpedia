-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeOne.cone_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:34.866671+00:00
-- url     : https://prove2.me/submissions/c38ac709-9d82-437e-aaad-31a203ecb5be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_radMeas_map
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_par_meas
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeOne
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
namespace GlobalTheory.HCXi.ConeOne
theorem _root_.solution (k r' : ℕ) (t : ℝ) (ht : 0 < t) :
    (coneMeas k r').map (fun v => (t : ℂ) • v) =
      ENNReal.ofReal ((t ^ (2 * (2 * r' + k + 1) + 2))⁻¹) • coneMeas k r' := by
  have hm : Measurable (fun c : ℂ => (t : ℂ) * c) := measurable_const_mul _
  have hs : Measurable (fun v : Fin (2 * (1 + r') + k + 1) → ℂ => (t : ℂ) • v) := measurable_const_smul _
  rw [cone_def, Measure.map_map hs (par_meas k r')]
  have e : (fun v : Fin (2 * (1 + r') + k + 1) → ℂ => (t : ℂ) • v) ∘ par k r' =
      par k r' ∘ Prod.map (fun c : ℂ => (t : ℂ) * c) id := by
    funext p
    simp only [Function.comp, par, Prod.map, id, smul_smul]
  rw [e, ← Measure.map_map (par_meas k r') (hm.prodMap measurable_id), ← Measure.map_prod_map _ _ hm measurable_id,
    radMeas_map _ t ht, Measure.map_id, Measure.prod_smul_left, Measure.map_smul]
end GlobalTheory.HCXi.ConeOne
