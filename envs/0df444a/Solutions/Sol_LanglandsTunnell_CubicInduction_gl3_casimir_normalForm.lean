-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.gl3_casimir_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/87424608-d8cb-54b0-9341-b432830f6f66

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_gl3_casimir_normalForm

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem solution
    {A : Type*} [Ring A] [Algebra ℂ A] (e : Fin 3 → Fin 3 → A)
    (he : ∀ i j k l : Fin 3,
      e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0)) :
    (∑ i : Fin 3, ∑ j : Fin 3, e i j * e j i =
      (e 0 0 * e 0 0 + e 1 1 * e 1 1 + e 2 2 * e 2 2 - 2 • e 0 0 + 2 • e 2 2) +
        (e 0 1 * (2 • e 1 0) + e 0 2 * (2 • e 2 0) + e 1 2 * (2 • e 2 1))) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, e i j * (e j k * e k i) =
      (e 0 0 * e 0 0 * e 0 0 + e 1 1 * e 1 1 * e 1 1 + e 2 2 * e 2 2 * e 2 2
        - 2 • (e 0 0 * e 0 0) + e 1 1 * e 1 1 + 4 • (e 2 2 * e 2 2)
        - (e 0 0 * e 1 1 + e 0 0 * e 2 2 + e 1 1 * e 2 2)
        - 2 • e 0 0 - 2 • e 1 1 + 4 • e 2 2) +
      (e 0 1 * (3 • (e 0 0 * e 1 0 + e 1 1 * e 1 0 + e 1 2 * e 2 0)) +
        e 0 2 * (3 • (e 0 0 * e 2 0 + e 1 0 * e 2 1 + e 2 0 + e 2 2 * e 2 0)) +
        e 1 2 * (3 • (e 1 1 * e 2 1 + 2 • e 2 1 + e 2 2 * e 2 1)))) := by
  have r1001 : (e 1 0 * e 0 1 - e 0 1 * e 1 0 - (e 1 1 - e 0 0)) = 0 := by
    have h := he 1 0 0 1
    rw [sub_eq_zero]
    simpa using h
  have r2002 : (e 2 0 * e 0 2 - e 0 2 * e 2 0 - (e 2 2 - e 0 0)) = 0 := by
    have h := he 2 0 0 2
    rw [sub_eq_zero]
    simpa using h
  have r2112 : (e 2 1 * e 1 2 - e 1 2 * e 2 1 - (e 2 2 - e 1 1)) = 0 := by
    have h := he 2 1 1 2
    rw [sub_eq_zero]
    simpa using h
  have r0001 : (e 0 0 * e 0 1 - e 0 1 * e 0 0 - (e 0 1)) = 0 := by
    have h := he 0 0 0 1
    rw [sub_eq_zero]
    simpa using h
  have r0002 : (e 0 0 * e 0 2 - e 0 2 * e 0 0 - (e 0 2)) = 0 := by
    have h := he 0 0 0 2
    rw [sub_eq_zero]
    simpa using h
  have r1000 : (e 1 0 * e 0 0 - e 0 0 * e 1 0 - (e 1 0)) = 0 := by
    have h := he 1 0 0 0
    rw [sub_eq_zero]
    simpa using h
  have r2000 : (e 2 0 * e 0 0 - e 0 0 * e 2 0 - (e 2 0)) = 0 := by
    have h := he 2 0 0 0
    rw [sub_eq_zero]
    simpa using h
  have r2110 : (e 2 1 * e 1 0 - e 1 0 * e 2 1 - (e 2 0)) = 0 := by
    have h := he 2 1 1 0
    rw [sub_eq_zero]
    simpa using h
  have r1002 : (e 1 0 * e 0 2 - e 0 2 * e 1 0 - (e 1 2)) = 0 := by
    have h := he 1 0 0 2
    rw [sub_eq_zero]
    simpa using h
  have r1112 : (e 1 1 * e 1 2 - e 1 2 * e 1 1 - (e 1 2)) = 0 := by
    have h := he 1 1 1 2
    rw [sub_eq_zero]
    simpa using h
  have r2001 : (e 2 0 * e 0 1 - e 0 1 * e 2 0 - (e 2 1)) = 0 := by
    have h := he 2 0 0 1
    rw [sub_eq_zero]
    simpa using h
  have r2111 : (e 2 1 * e 1 1 - e 1 1 * e 2 1 - (e 2 1)) = 0 := by
    have h := he 2 1 1 1
    rw [sub_eq_zero]
    simpa using h
  have r1011 : (e 1 0 * e 1 1 - e 1 1 * e 1 0 - (-e 1 0)) = 0 := by
    have h := he 1 0 1 1
    rw [sub_eq_zero]
    simpa using h
  have r1101 : (e 1 1 * e 0 1 - e 0 1 * e 1 1 - (-e 0 1)) = 0 := by
    have h := he 1 1 0 1
    rw [sub_eq_zero]
    simpa using h
  have r1100 : (e 1 1 * e 0 0 - e 0 0 * e 1 1 - (0)) = 0 := by
    have h := he 1 1 0 0
    rw [sub_eq_zero]
    simpa using h
  have r1201 : (e 1 2 * e 0 1 - e 0 1 * e 1 2 - (-e 0 2)) = 0 := by
    have h := he 1 2 0 1
    rw [sub_eq_zero]
    simpa using h
  have r2012 : (e 2 0 * e 1 2 - e 1 2 * e 2 0 - (-e 1 0)) = 0 := by
    have h := he 2 0 1 2
    rw [sub_eq_zero]
    simpa using h
  have r2022 : (e 2 0 * e 2 2 - e 2 2 * e 2 0 - (-e 2 0)) = 0 := by
    have h := he 2 0 2 2
    rw [sub_eq_zero]
    simpa using h
  have r2102 : (e 2 1 * e 0 2 - e 0 2 * e 2 1 - (-e 0 1)) = 0 := by
    have h := he 2 1 0 2
    rw [sub_eq_zero]
    simpa using h
  have r2122 : (e 2 1 * e 2 2 - e 2 2 * e 2 1 - (-e 2 1)) = 0 := by
    have h := he 2 1 2 2
    rw [sub_eq_zero]
    simpa using h
  have r2202 : (e 2 2 * e 0 2 - e 0 2 * e 2 2 - (-e 0 2)) = 0 := by
    have h := he 2 2 0 2
    rw [sub_eq_zero]
    simpa using h
  have r2200 : (e 2 2 * e 0 0 - e 0 0 * e 2 2 - (0)) = 0 := by
    have h := he 2 2 0 0
    rw [sub_eq_zero]
    simpa using h
  have r2212 : (e 2 2 * e 1 2 - e 1 2 * e 2 2 - (-e 1 2)) = 0 := by
    have h := he 2 2 1 2
    rw [sub_eq_zero]
    simpa using h
  have r2211 : (e 2 2 * e 1 1 - e 1 1 * e 2 2 - (0)) = 0 := by
    have h := he 2 2 1 1
    rw [sub_eq_zero]
    simpa using h
  constructor
  · have key : (∑ i : Fin 3, ∑ j : Fin 3, e i j * e j i) - ((e 0 0 * e 0 0 + e 1 1 * e 1 1 + e 2 2 * e 2 2 - 2 • e 0 0 + 2 • e 2 2) + (e 0 1 * (2 • e 1 0) + e 0 2 * (2 • e 2 0) + e 1 2 * (2 • e 2 1))) =
        ((e 1 0 * e 0 1 - e 0 1 * e 1 0 - (e 1 1 - e 0 0))) + ((e 2 0 * e 0 2 - e 0 2 * e 2 0 - (e 2 2 - e 0 0))) + ((e 2 1 * e 1 2 - e 1 2 * e 2 1 - (e 2 2 - e 1 1))) := by
      simp only [Fin.sum_univ_three, Fin.isValue, nsmul_eq_mul, Nat.cast_ofNat]
      noncomm_ring
    rw [r1001, r2002, r2112] at key
    rw [← sub_eq_zero, key]
    simp
  · have key : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, e i j * (e j k * e k i)) - ((e 0 0 * e 0 0 * e 0 0 + e 1 1 * e 1 1 * e 1 1 + e 2 2 * e 2 2 * e 2 2 - 2 • (e 0 0 * e 0 0) + e 1 1 * e 1 1 + 4 • (e 2 2 * e 2 2) - (e 0 0 * e 1 1 + e 0 0 * e 2 2 + e 1 1 * e 2 2) - 2 • e 0 0 - 2 • e 1 1 + 4 • e 2 2) + (e 0 1 * (3 • (e 0 0 * e 1 0 + e 1 1 * e 1 0 + e 1 2 * e 2 0)) + e 0 2 * (3 • (e 0 0 * e 2 0 + e 1 0 * e 2 1 + e 2 0 + e 2 2 * e 2 0)) + e 1 2 * (3 • (e 1 1 * e 2 1 + 2 • e 2 1 + e 2 2 * e 2 1)))) =
        2 * ((e 0 0 * e 0 1 - e 0 1 * e 0 0 - (e 0 1)) * e 1 0) + 2 * ((e 0 0 * e 0 2 - e 0 2 * e 0 0 - (e 0 2)) * e 2 0) + (e 0 1 * (e 1 0 * e 0 0 - e 0 0 * e 1 0 - (e 1 0))) + (e 0 2 * (e 2 0 * e 0 0 - e 0 0 * e 2 0 - (e 2 0))) + (e 0 2 * (e 2 1 * e 1 0 - e 1 0 * e 2 1 - (e 2 0))) + ((e 1 0 * e 0 0 - e 0 0 * e 1 0 - (e 1 0)) * e 0 1) + ((e 1 0 * e 0 1 - e 0 1 * e 1 0 - (e 1 1 - e 0 0)) * e 1 1) + 2 * ((e 1 0 * e 0 2 - e 0 2 * e 1 0 - (e 1 2)) * e 2 1) + (e 1 1 * (e 1 0 * e 0 1 - e 0 1 * e 1 0 - (e 1 1 - e 0 0))) + 2 * ((e 1 1 * e 1 2 - e 1 2 * e 1 1 - (e 1 2)) * e 2 1) + (e 1 2 * (e 2 0 * e 0 1 - e 0 1 * e 2 0 - (e 2 1))) + (e 1 2 * (e 2 1 * e 1 1 - e 1 1 * e 2 1 - (e 2 1))) + ((e 2 0 * e 0 0 - e 0 0 * e 2 0 - (e 2 0)) * e 0 2) + ((e 2 0 * e 0 1 - e 0 1 * e 2 0 - (e 2 1)) * e 1 2) + ((e 2 0 * e 0 2 - e 0 2 * e 2 0 - (e 2 2 - e 0 0)) * e 2 2) + ((e 2 1 * e 1 0 - e 1 0 * e 2 1 - (e 2 0)) * e 0 2) + ((e 2 1 * e 1 1 - e 1 1 * e 2 1 - (e 2 1)) * e 1 2) + ((e 2 1 * e 1 2 - e 1 2 * e 2 1 - (e 2 2 - e 1 1)) * e 2 2) + (e 2 2 * (e 2 0 * e 0 2 - e 0 2 * e 2 0 - (e 2 2 - e 0 0))) + (e 2 2 * (e 2 1 * e 1 2 - e 1 2 * e 2 1 - (e 2 2 - e 1 1))) + (e 0 0 * (e 1 0 * e 0 1 - e 0 1 * e 1 0 - (e 1 1 - e 0 0))) + (e 0 1 * (e 1 0 * e 1 1 - e 1 1 * e 1 0 - (-e 1 0))) + ((e 1 1 * e 0 1 - e 0 1 * e 1 1 - (-e 0 1)) * e 1 0) - ((e 1 1 * e 0 0 - e 0 0 * e 1 1 - (0))) + ((e 1 2 * e 0 1 - e 0 1 * e 1 2 - (-e 0 2)) * e 2 0) + (e 0 0 * (e 2 0 * e 0 2 - e 0 2 * e 2 0 - (e 2 2 - e 0 0))) + 2 * ((e 2 0 * e 0 2 - e 0 2 * e 2 0 - (e 2 2 - e 0 0))) + (e 0 1 * (e 2 0 * e 1 2 - e 1 2 * e 2 0 - (-e 1 0))) + 2 * ((e 2 1 * e 1 2 - e 1 2 * e 2 1 - (e 2 2 - e 1 1))) + (e 0 2 * (e 2 0 * e 2 2 - e 2 2 * e 2 0 - (-e 2 0))) + (e 1 0 * (e 2 1 * e 0 2 - e 0 2 * e 2 1 - (-e 0 1))) + (e 1 1 * (e 2 1 * e 1 2 - e 1 2 * e 2 1 - (e 2 2 - e 1 1))) + (e 1 2 * (e 2 1 * e 2 2 - e 2 2 * e 2 1 - (-e 2 1))) + ((e 2 2 * e 0 2 - e 0 2 * e 2 2 - (-e 0 2)) * e 2 0) - ((e 2 2 * e 0 0 - e 0 0 * e 2 2 - (0))) + ((e 2 2 * e 1 2 - e 1 2 * e 2 2 - (-e 1 2)) * e 2 1) - ((e 2 2 * e 1 1 - e 1 1 * e 2 2 - (0))) := by
      simp only [Fin.sum_univ_three, Fin.isValue, nsmul_eq_mul, Nat.cast_ofNat]
      noncomm_ring
    rw [r1001, r2002, r2112, r0001, r0002, r1000, r2000, r2110, r1002, r1112, r2001, r2111, r1011, r1101, r1100, r1201, r2012, r2022, r2102, r2122, r2202, r2200, r2212, r2211] at key
    rw [← sub_eq_zero, key]
    simp

end S_LanglandsTunnell_CubicInduction_gl3_casimir_normalForm
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_gl3_casimir_normalForm (solution)
