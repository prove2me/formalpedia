-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeOne.cone_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:53.625879+00:00
-- url     : https://prove2.me/submissions/229f5782-8232-46b2-83a3-053abefd8290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_map
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_sqLen_cont
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_sqLen_smul

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
theorem _root_.solution (k r' : ℕ) (s : ℝ) (hs : 0 < s) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, f (s * sqLen v) ∂(coneMeas k r')) =
      ENNReal.ofReal (s ^ (-((2 * (1 + r') + k : ℕ) : ℝ))) * ∫⁻ v, f (sqLen v) ∂(coneMeas k r') := by
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsm : Measurable (fun v : Fin (2 * (1 + r') + k + 1) → ℂ => ((Real.sqrt s : ℝ) : ℂ) • v) :=
    measurable_const_smul _
  have h1 := lintegral_map (μ := coneMeas k r') (hf.comp sqLen_cont.measurable) hsm
  rw [cone_map k r' _ ht, lintegral_smul_measure] at h1
  simp only [Function.comp, sqLen_smul, Real.sq_sqrt hs.le] at h1
  rw [← h1, smul_eq_mul]
  congr 2
  rw [Real.rpow_neg hs.le, Real.rpow_natCast,
    show 2 * (2 * r' + k + 1) + 2 = 2 * (2 * (1 + r') + k) by ring, pow_mul, Real.sq_sqrt hs.le]
end GlobalTheory.HCXi.ConeOne
