-- Prove2me | solution 1 for GlobalTheory.CuspGL.mangoldtConv_finite_monicDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:05:36.500476+00:00
-- url     : https://prove2.me/submissions/ba84ca79-3455-4c92-86d0-40b43cbc477f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (P : F[X]) (hP : P.Monic) :
    {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by
  have := Polynomial.fintypeSubtypeMonicDvd P hP.ne_zero
  exact Set.finite_coe_iff.mp (Finite.of_fintype {g : F[X] // g.Monic ∧ g ∣ P})
end GlobalTheory.CuspGL
