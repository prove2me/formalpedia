-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent.signedCharacteristicProjector_eigen_of_aeval_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/91fec144-7a06-4581-bf32-ee467957d2b7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCompressedResolvent_signedNode_sub_mul_basis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
theorem _root_.solution
    {r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : Fin (r + 1) → ℝ) (T : Module.End ℝ V)
    (i : Fin (r + 1) × Bool) (v : V)
    (hchar : Polynomial.aeval T (signedAmbientCharacteristic L) v = 0) :
    T (signedCharacteristicProjector L T i v) =
      signedNode L i • signedCharacteristicProjector L T i v := by
  have hzero := congrArg (Polynomial.aeval T)
    (signedNode_sub_mul_basis L i)
  simp only [map_mul, Polynomial.aeval_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at hzero
  have happly := LinearMap.congr_fun hzero v
  apply sub_eq_zero.mp
  simpa [signedCharacteristicProjector,
    Module.algebraMap_end_eq_smul_id,
    LinearMap.sub_apply, hchar] using happly
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
