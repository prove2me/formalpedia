-- Prove2me | solution 1 for GlobalTheory.CuspGL.pow_card_pow_eq_iff_natDegree_minpoly_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:08:14.580067+00:00
-- url     : https://prove2.me/submissions/13462a1e-cd81-4a4f-8abc-ac1a3ff15b03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F]
    (α : AlgebraicClosure F) (e : ℕ) :
    α ^ Nat.card F ^ e = α ↔ (minpoly F α).natDegree ∣ e := by
  classical
  have := Fintype.ofFinite F
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have : FiniteDimensional F (IntermediateField.adjoin F {α}) := IntermediateField.adjoin.finiteDimensional hx
  have : Finite (IntermediateField.adjoin F {α}) := Module.finite_of_finite F
  have hgen : ∀ m : ℕ, (FiniteField.frobeniusAlgEquivOfAlgebraic F (IntermediateField.adjoin F {α}) ^ m)
      (IntermediateField.AdjoinSimple.gen F α) =
      IntermediateField.AdjoinSimple.gen F α ^ (Fintype.card F ^ m) := by
    intro m
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [← IntermediateField.adjoin.finrank hx,
    ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F (IntermediateField.adjoin F {α}), orderOf_dvd_iff_pow_eq_one,
    Nat.card_eq_fintype_card]
  constructor
  · intro h
    apply AlgEquiv.coe_toAlgHom_injective
    apply (IntermediateField.adjoin.powerBasis hx).algHom_ext
    rw [IntermediateField.adjoin.powerBasis_gen hx]
    simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.one_apply]
    rw [hgen]
    apply Subtype.ext
    simpa using h
  · intro h
    have key := congrArg (fun f => ((f (IntermediateField.AdjoinSimple.gen F α) : (IntermediateField.adjoin F {α})) :
      AlgebraicClosure F)) h
    simp only [hgen, AlgEquiv.one_apply] at key
    simpa using key
end GlobalTheory.CuspGL
