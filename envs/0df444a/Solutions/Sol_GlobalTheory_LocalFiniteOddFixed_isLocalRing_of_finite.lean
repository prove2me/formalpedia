-- Prove2me | solution 1 for GlobalTheory.LocalFiniteOddFixed.isLocalRing_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:17.620832+00:00
-- url     : https://prove2.me/submissions/bed04cc8-27c0-48a0-b1bc-749ff7fe80d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite
import Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_precomplete_of_finite
import Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_exists_pow_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
namespace GlobalTheory.LocalFiniteOddFixed
theorem _root_.solution (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (R : Type) [CommRing R] [IsDomain R] [Algebra O R] [Module.Finite O R] : IsLocalRing R := by
  set J : Ideal R := (IsLocalRing.maximalIdeal O).map (algebraMap O R) with hJ
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal O) R := precomplete_of_finite O _ R
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) R := {}
  haveI : IsAdicComplete J R := (IsAdicComplete.map_algebraMap_iff _ R).2 inferInstance
  haveI hH : HenselianRing R J := IsAdicComplete.henselianRing R J
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (R ⧸ J) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (R ⧸ J) := Module.finite_of_finite (O ⧸ IsLocalRing.maximalIdeal O)
  have hjac : ∀ y ∈ J, IsUnit (1 + y) := by
    intro y hy
    have := Ideal.mem_jacobson_bot.1 (hH.jac hy) 1
    simpa [add_comm] using this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨n, hn, h⟩ := exists_pow_idem (R ⧸ J) (Ideal.Quotient.mk J x)
  have hm : (X ^ 2 - X : R[X]).Monic := by monicity!
  obtain ⟨e, he, hex⟩ := hH.is_henselian (X ^ 2 - X) hm (x ^ n)
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow]
      rw [sq, h, sub_self])
    (by
      have : Ideal.Quotient.mk J (eval (x ^ n) (derivative (X ^ 2 - X : R[X])))
          = 2 * (Ideal.Quotient.mk J x) ^ n - 1 := by
        simp
        ring
      rw [this]
      refine IsUnit.of_mul_eq_one (2 * (Ideal.Quotient.mk J x) ^ n - 1) ?_
      linear_combination 4 * h)
  have he' : e * (e - 1) = 0 := by
    have : e ^ 2 - e = 0 := by simpa using he
    linear_combination this
  rcases mul_eq_zero.1 he' with h0 | h1
  · right
    rw [h0, zero_sub] at hex
    have hu := hjac _ hex
    rw [← sub_eq_add_neg, ← mul_neg_geom_sum] at hu
    exact isUnit_of_mul_isUnit_left hu
  · left
    have h1' : e = 1 := sub_eq_zero.1 h1
    rw [h1'] at hex
    have hu := hjac _ (J.neg_mem hex)
    have : 1 + -(1 - x ^ n) = x ^ n := by ring
    rw [this] at hu
    exact (isUnit_pow_iff hn.ne').1 hu
end GlobalTheory.LocalFiniteOddFixed
