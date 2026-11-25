-- Prove2me | solution 1 for GlobalTheory.HCXi.isUnit_det_gram_of_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:55.541467+00:00
-- url     : https://prove2.me/submissions/9682f73d-280c-4fc6-9d88-c6f048b08f43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsUnitaryOfGramEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsQr
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi
namespace GlobalTheory.HCXi
theorem _root_.solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (L : Matrix (Fin m) (Fin n) ℂ)
    (h : L * A = 1) : IsUnit (Aᴴ * A).det := by
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have h2 := congrArg L.mulVec hxy
    simpa [Matrix.mulVec_mulVec, h] using h2
  have hp : (Aᴴ * A).PosDef := Matrix.PosDef.conjTranspose_mul_self A hinj
  exact (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
end GlobalTheory.HCXi
