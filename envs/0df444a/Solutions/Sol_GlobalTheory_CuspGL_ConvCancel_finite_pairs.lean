-- Prove2me | solution 1 for GlobalTheory.CuspGL.ConvCancel.finite_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:02:45.791599+00:00
-- url     : https://prove2.me/submissions/a7e857e1-805b-47ee-8211-30a8c204d33f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionCancelOfOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.ConvCancel
namespace GlobalTheory.CuspGL.ConvCancel
theorem _root_.solution {F : Type} [Field F] (P : F[X]) (hP : P ≠ 0) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  classical
  have hfin : {g : F[X] | g.Monic ∧ g ∣ P}.Finite := by
    have h := Polynomial.fintypeSubtypeMonicDvd P hP
    exact @Finite.of_fintype _ h
  refine (hfin.prod hfin).subset ?_
  rintro ⟨D, E⟩ ⟨hD, hE, h⟩
  exact ⟨⟨hD, Dvd.intro _ h⟩, ⟨hE, Dvd.intro_left _ h⟩⟩
end GlobalTheory.CuspGL.ConvCancel
