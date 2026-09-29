-- Prove2me | solution 1 for ModularCurve.evalModularPair_jFun_jNFun_jQFun_jNQFun_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/1349685f-876e-5e87-9f14-67a923b6c7ac

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_MDivRepresents
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_evalModularPair_jFun_jNFun_jQFun_jNQFun_eq_zero
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve
open ModularCurve.PlaceSpecialization

namespace ModEq

section Coeff

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem coeffMap_qExpand' (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

end Coeff

private theorem coeffEmb_jq' : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) :=
  map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem coeffEmb_jqN' (n : ℕ) [NeZero n] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n jq) = jqNModC (AlgebraicClosure ℚ) n := by
  have h := coeffMap_qExpand' (algebraMap ℚ (AlgebraicClosure ℚ)) n jq
  rw [jqNModC, ← coeffEmb_jq']
  exact h

variable (N q : ℕ) [NeZero N] [NeZero q]

private theorem coe_jFun :
    ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) := coeffEmb_jq'

private theorem coe_jQFun :
    ((ProlongationTuple.jQFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = jqNModC (AlgebraicClosure ℚ) q := coeffEmb_jqN' q

private theorem coe_jNFun :
    ((PlaceSpecialization.jNFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = jqNModC (AlgebraicClosure ℚ) N := coeffEmb_jqN' N

private theorem coe_jNQFun :
    ((PlaceSpecialization.jNQFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = jqNModC (AlgebraicClosure ℚ) (N * q) := coeffEmb_jqN' (N * q)

private theorem evalModularPair_eq_zero_laurent (dataN : ModularPolynomialData N) (dataq : ModularPolynomialData q) :
    evalModularPair (jqModC (AlgebraicClosure ℚ)) (jqNModC (AlgebraicClosure ℚ) N) dataN.Φ = 0 ∧
    evalModularPair (jqNModC (AlgebraicClosure ℚ) q) (jqNModC (AlgebraicClosure ℚ) (N * q)) dataN.Φ = 0 ∧
    evalModularPair (jqModC (AlgebraicClosure ℚ)) (jqNModC (AlgebraicClosure ℚ) q) dataq.Φ = 0 ∧
    evalModularPair (jqNModC (AlgebraicClosure ℚ) N) (jqNModC (AlgebraicClosure ℚ) (N * q)) dataq.Φ = 0 := by
  have h1 := evalModularPair_jq_eq_zero (AlgebraicClosure ℚ) dataN
  have h3 := evalModularPair_jq_eq_zero (AlgebraicClosure ℚ) dataq
  refine ⟨h1, ?_, h3, ?_⟩
  ·
    have e1 : jqNModC (AlgebraicClosure ℚ) q = qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)) := rfl
    have e2 : jqNModC (AlgebraicClosure ℚ) (N * q)
        = qExpand (AlgebraicClosure ℚ) q (jqNModC (AlgebraicClosure ℚ) N) := by
      unfold jqNModC
      rw [qExpand_qExpand, qExpand_congr (mul_comm q N)]
    have h := map_evalModularPair (qExpand (AlgebraicClosure ℚ) q) (jqModC (AlgebraicClosure ℚ))
      (jqNModC (AlgebraicClosure ℚ) N) dataN.Φ
    rw [h1, map_zero] at h
    rw [e1, e2]
    exact h.symm
  ·
    have e1 : jqNModC (AlgebraicClosure ℚ) N = qExpand (AlgebraicClosure ℚ) N (jqModC (AlgebraicClosure ℚ)) := rfl
    have e2 : jqNModC (AlgebraicClosure ℚ) (N * q)
        = qExpand (AlgebraicClosure ℚ) N (jqNModC (AlgebraicClosure ℚ) q) := by
      unfold jqNModC
      rw [qExpand_qExpand]
    have h := map_evalModularPair (qExpand (AlgebraicClosure ℚ) N) (jqModC (AlgebraicClosure ℚ))
      (jqNModC (AlgebraicClosure ℚ) q) dataq.Φ
    rw [h3, map_zero] at h
    rw [e1, e2]
    exact h.symm

omit [NeZero N] [NeZero q] in

private theorem evalModularPair_eq_zero_of_coe (x y : ↥(modularFunctionFieldBar (N * q))) (Φ : Polynomial (Polynomial ℤ))
    (h : evalModularPair (x : LaurentSeries (AlgebraicClosure ℚ)) (y : LaurentSeries (AlgebraicClosure ℚ)) Φ = 0) :
    evalModularPair x y Φ = 0 := by
  have hval := map_evalModularPair (modularFunctionFieldBar (N * q)).val.toRingHom x y Φ
  have hx : (modularFunctionFieldBar (N * q)).val.toRingHom x = (x : LaurentSeries (AlgebraicClosure ℚ)) := rfl
  have hy : (modularFunctionFieldBar (N * q)).val.toRingHom y = (y : LaurentSeries (AlgebraicClosure ℚ)) := rfl
  rw [hx, hy, h] at hval
  exact (map_eq_zero_iff _ (modularFunctionFieldBar (N * q)).val.toRingHom.injective).mp hval

end ModEq

open ModEq in

theorem solution
    (N q : ℕ) [NeZero N] [Fact q.Prime]
    (dataN : ModularPolynomialData N) (dataq : ModularPolynomialData q) :
    evalModularPair (PlaceSpecialization.ProlongationTuple.jFun N q) (PlaceSpecialization.jNFun N q) dataN.Φ = 0 ∧
    evalModularPair (PlaceSpecialization.ProlongationTuple.jQFun N q) (PlaceSpecialization.jNQFun N q) dataN.Φ = 0 ∧
    evalModularPair (PlaceSpecialization.ProlongationTuple.jFun N q) (PlaceSpecialization.ProlongationTuple.jQFun N q) dataq.Φ = 0 ∧
    evalModularPair (PlaceSpecialization.jNFun N q) (PlaceSpecialization.jNQFun N q) dataq.Φ = 0 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨h1, h2, h3, h4⟩ := evalModularPair_eq_zero_laurent N q dataN dataq
  refine ⟨evalModularPair_eq_zero_of_coe N q _ _ _ ?_, evalModularPair_eq_zero_of_coe N q _ _ _ ?_,
    evalModularPair_eq_zero_of_coe N q _ _ _ ?_, evalModularPair_eq_zero_of_coe N q _ _ _ ?_⟩
  · rw [coe_jFun, coe_jNFun]; exact h1
  · rw [coe_jQFun, coe_jNQFun]; exact h2
  · rw [coe_jFun, coe_jQFun]; exact h3
  · rw [coe_jNFun, coe_jNQFun]; exact h4

end S_ModularCurve_evalModularPair_jFun_jNFun_jQFun_jNQFun_eq_zero
end P2MW
export P2MW.S_ModularCurve_evalModularPair_jFun_jNFun_jQFun_jNQFun_eq_zero (solution)
