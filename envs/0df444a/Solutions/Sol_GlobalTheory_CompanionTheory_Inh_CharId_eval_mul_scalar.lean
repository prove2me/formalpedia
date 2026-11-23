-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CharId.eval_mul_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:37.739284+00:00
-- url     : https://prove2.me/submissions/53f778b3-f4b7-4db7-87c3-22db382b1fd3

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset TensorProduct Formalism.HermitianLatticeCounting.S8
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Inh GlobalTheory.CompanionTheory.Inh.CharId
open Polynomial Formalism.REAL
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace GlobalTheory.CompanionTheory.Inh.CharId
theorem _root_.solution (P Q : B[X]) (u : ℂ) :
    (P * Q).eval (algebraMap ℂ B u) = P.eval (algebraMap ℂ B u) * Q.eval (algebraMap ℂ B u) := by
  have := Polynomial.eval₂_mul_noncomm (p := P) (q := Q) (RingHom.id B) (algebraMap ℂ B u)
    (fun k => (Algebra.commutes u _).symm)
  exact this
end GlobalTheory.CompanionTheory.Inh.CharId
