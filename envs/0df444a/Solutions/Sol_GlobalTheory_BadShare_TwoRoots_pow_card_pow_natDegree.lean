-- Prove2me | solution 1 for GlobalTheory.BadShare.TwoRoots.pow_card_pow_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:47:47.054575+00:00
-- url     : https://prove2.me/submissions/1bdeed5f-5072-46bf-be1d-38b620e80b55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.TwoRoots
namespace GlobalTheory.BadShare.TwoRoots
theorem _root_.solution {g : ℕ} [Fact g.Prime] (x : AlgebraicClosure (ZMod g)) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree) = x := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  haveI : Fintype (IntermediateField.adjoin (ZMod g) {x}) := Fintype.ofFinite _
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have h := FiniteField.pow_card y
  rw [Module.card_eq_pow_finrank (K := ZMod g), IntermediateField.adjoin.finrank hi, ZMod.card] at h
  simpa [y] using congrArg Subtype.val h
end GlobalTheory.BadShare.TwoRoots
