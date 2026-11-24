-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistSL.map_cast_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:37.9628+00:00
-- url     : https://prove2.me/submissions/4a52f67d-21db-453c-8a49-4fa31834b9c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMulSL2Z

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistSL
namespace GlobalTheory.HilbFam.TwistSL
theorem _root_.solution (R : Type) [CommRing R] (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B).map (Int.cast : ℤ → R) = A.map (Int.cast : ℤ → R) * B.map (Int.cast : ℤ → R) :=
  Matrix.map_mul (f := Int.castRingHom R)
end GlobalTheory.HilbFam.TwistSL
