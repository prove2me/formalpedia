-- Prove2me | solution 1 for GlobalTheory.HCXi.gram_unitary_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:05.65304+00:00
-- url     : https://prove2.me/submissions/85c24f82-d061-42e9-82d3-1ace46fdb1aa

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
theorem _root_.solution (k r : ℕ) (κ g : Mat k r) (hκ : κᴴ * κ = 1) (a : Fin (r + 1)) :
    gram k r (κ * g) a = gram k r g a := by
  have h : (κ * g * frame k r)ᴴ * (κ * g * frame k r) = (g * frame k r)ᴴ * (g * frame k r) := by
    rw [Matrix.mul_assoc κ g, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]
  unfold gram
  rw [h]
end GlobalTheory.HCXi
