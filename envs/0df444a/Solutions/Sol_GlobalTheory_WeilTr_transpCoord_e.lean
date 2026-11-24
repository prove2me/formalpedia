-- Prove2me | solution 1 for GlobalTheory.WeilTr.transpCoord_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:39.396292+00:00
-- url     : https://prove2.me/submissions/98da61bd-1932-4cec-a1ae-7ffcd9631dd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUSplittingTrRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.WeilTr
open GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}
namespace GlobalTheory.WeilTr
theorem _root_.solution {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {α β : Type} [Fintype α] [Fintype β] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    (d : Darboux (symp c ξ JA JB) κ) (x : Matrix α β E) : (transpCoord d).e xᵀ = d.e x := rfl
end GlobalTheory.WeilTr
