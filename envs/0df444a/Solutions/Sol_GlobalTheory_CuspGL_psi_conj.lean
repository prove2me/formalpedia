-- Prove2me | solution 1 for GlobalTheory.CuspGL.psi_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:23:40.498354+00:00
-- url     : https://prove2.me/submissions/47e82175-0b0a-4ffa-ae48-8bc4496b6c9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Theorems.Thm_GlobalTheory_CuspGL_invariantSubspaceMobiusInverseRec_linearEquiv_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
open Polynomial
namespace GlobalTheory.CuspGL
namespace _root_.GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F]
    (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
    (e : V ≃ₗ[F] V') (g : Module.End F V) :
    _root_.GlobalTheory.CuspGL.psi s V' (e.conj g) =
      _root_.GlobalTheory.CuspGL.psi s V g := by
  unfold _root_.GlobalTheory.CuspGL.psi
  rw [← e.finrank_eq]
  exact _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj s _ V V' e g
end _root_.GlobalTheory.CuspGL
end GlobalTheory.CuspGL
