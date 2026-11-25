-- Prove2me | solution 1 for GlobalTheory.HCXi.gram_nonneg_vmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:18.167089+00:00
-- url     : https://prove2.me/submissions/6ee059e1-3b77-4940-95c8-3116699d8836

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariant

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
theorem _root_.solution (k r : ℕ) (g : Mat k r) (a : Fin (r + 1)) : 0 ≤ gram k r g a := by
  unfold gram
  have h := ((Matrix.posSemidef_conjTranspose_mul_self (g * frame k r)).submatrix
    (Fin.castLE (Nat.succ_le_of_lt a.isLt))).det_nonneg
  exact (Complex.nonneg_iff.mp h).1
end GlobalTheory.HCXi
