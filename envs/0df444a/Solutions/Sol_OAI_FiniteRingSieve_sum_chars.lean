-- Prove2me | solution 1 for OAI.FiniteRingSieve.sum_chars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:37.131848+00:00
-- url     : https://prove2.me/submissions/2a323138-bd36-48b7-b9e4-6dc3bd545ead

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftMellin
end ShortDraftMellin
namespace FiniteRingSieve
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
attribute [local instance] logProfilesFintypeMulChar
omit [DecidableEq R] in
private theorem sum_chars_zero {a : R} (ha : a ≠ 1) :
    (∑ χ : MulChar R ℂ, χ a) = 0 := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity R ℂ ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' => rfl
end FiniteRingSieve
namespace FiniteFieldSieve
variable {F : Type*} [Field F] [Fintype F]
end FiniteFieldSieve
namespace ProductResidueSieve
variable {R S : Type*} [CommRing R] [CommRing S]
end ProductResidueSieve
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
namespace FourierBridge
end FourierBridge
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.FiniteRingSieve
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
attribute [local instance] OAI.FiniteRingSieve.logProfilesFintypeMulChar
attribute [local instance] logProfilesFintypeMulChar
namespace OAI.FiniteRingSieve
theorem _root_.solution (a : R) :
    (∑ χ : MulChar R ℂ, χ a) =
      if a = 1 then (Fintype.card Rˣ : ℂ) else 0 := by
  split_ifs with ha
  · subst a
    simp only [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hc : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
      simpa only [Nat.card_eq_fintype_card] using
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ
    exact_mod_cast hc
  · exact sum_chars_zero ha
end OAI.FiniteRingSieve
