-- Prove2me | solution 1 for OAI.DimensionTen.Mod139.iterate18
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:16:41.690047+00:00
-- url     : https://prove2.me/submissions/a19374bd-3104-404f-8213-bc50909e5dd1

import Mathlib
import Definitions.Def_OAIQ033D013
import Theorems.Thm_OAI_DimensionTen_Mod139_iterate12

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers07
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow13_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z + (139 : R) * pow13_2_mul_t z := by
  simp only [u12, pow13_2_q, f, pow13_2, pow13_2_mul_t]
  simp only [pow12_139]
  ring

theorem pow13_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_2_mul_integer z


theorem pow13_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z * u12 z = pow13_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_2_mul z


theorem pow13_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 2 = pow13_2 z := by
  calc
    _ = u12 z ^ 1 * u12 z ^ 1 := by ring
    _ = u12 z * u12 z := by simp only [pow_one]
    _ = _ := pow13_2_root z hz


theorem pow13_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z + (139 : R) * pow13_4_mul_t z := by
  simp only [pow13_2, pow13_4_q, f, pow13_4, pow13_4_mul_t]
  
  ring

theorem pow13_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_4_mul_integer z


theorem pow13_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_2 z * pow13_2 z = pow13_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_4_mul z


theorem pow13_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 4 = pow13_4 z := by
  calc
    _ = u12 z ^ 2 * u12 z ^ 2 := by ring
    _ = pow13_2 z * pow13_2 z := by rw [pow13_2_pow z hz]
    _ = _ := pow13_4_root z hz


theorem pow13_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_4 z * pow13_4 z = pow13_8_q z * f z + pow13_8 z + (139 : R) * pow13_8_mul_t z := by
  simp only [pow13_4, pow13_8_q, f, pow13_8, pow13_8_mul_t]
  
  ring

theorem pow13_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_4 z * pow13_4 z = pow13_8_q z * f z + pow13_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_8_mul_integer z


theorem pow13_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_4 z * pow13_4 z = pow13_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_8_mul z


theorem pow13_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 8 = pow13_8 z := by
  calc
    _ = u12 z ^ 4 * u12 z ^ 4 := by ring
    _ = pow13_4 z * pow13_4 z := by rw [pow13_4_pow z hz]
    _ = _ := pow13_8_root z hz


theorem pow13_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_8 z * pow13_8 z = pow13_16_q z * f z + pow13_16 z + (139 : R) * pow13_16_mul_t z := by
  simp only [pow13_8, pow13_16_q, f, pow13_16, pow13_16_mul_t]
  
  ring

theorem pow13_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_8 z * pow13_8 z = pow13_16_q z * f z + pow13_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_16_mul_integer z


theorem pow13_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_8 z * pow13_8 z = pow13_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_16_mul z


theorem pow13_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 16 = pow13_16 z := by
  calc
    _ = u12 z ^ 8 * u12 z ^ 8 := by ring
    _ = pow13_8 z * pow13_8 z := by rw [pow13_8_pow z hz]
    _ = _ := pow13_16_root z hz


theorem pow13_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_16 z * u12 z = pow13_17_q z * f z + pow13_17 z + (139 : R) * pow13_17_mul_t z := by
  simp only [pow13_16, u12, pow13_17_q, f, pow13_17, pow13_17_mul_t]
  simp only [pow12_139]
  ring

theorem pow13_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_16 z * u12 z = pow13_17_q z * f z + pow13_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_17_mul_integer z


theorem pow13_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_16 z * u12 z = pow13_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_17_mul z


theorem pow13_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 17 = pow13_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow13_16_pow z hz]
  exact pow13_17_root z hz


theorem pow13_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_17 z * pow13_17 z = pow13_34_q z * f z + pow13_34 z + (139 : R) * pow13_34_mul_t z := by
  simp only [pow13_17, pow13_34_q, f, pow13_34, pow13_34_mul_t]
  
  ring

theorem pow13_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_17 z * pow13_17 z = pow13_34_q z * f z + pow13_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_34_mul_integer z


theorem pow13_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_17 z * pow13_17 z = pow13_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_34_mul z


theorem pow13_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 34 = pow13_34 z := by
  calc
    _ = u12 z ^ 17 * u12 z ^ 17 := by ring
    _ = pow13_17 z * pow13_17 z := by rw [pow13_17_pow z hz]
    _ = _ := pow13_34_root z hz


theorem pow13_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_34 z * pow13_34 z = pow13_68_q z * f z + pow13_68 z + (139 : R) * pow13_68_mul_t z := by
  simp only [pow13_34, pow13_68_q, f, pow13_68, pow13_68_mul_t]
  
  ring

theorem pow13_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_34 z * pow13_34 z = pow13_68_q z * f z + pow13_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_68_mul_integer z


theorem pow13_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_34 z * pow13_34 z = pow13_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_68_mul z


theorem pow13_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 68 = pow13_68 z := by
  calc
    _ = u12 z ^ 34 * u12 z ^ 34 := by ring
    _ = pow13_34 z * pow13_34 z := by rw [pow13_34_pow z hz]
    _ = _ := pow13_68_root z hz


theorem pow13_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_68 z * u12 z = pow13_69_q z * f z + pow13_69 z + (139 : R) * pow13_69_mul_t z := by
  simp only [pow13_68, u12, pow13_69_q, f, pow13_69, pow13_69_mul_t]
  simp only [pow12_139]
  ring

theorem pow13_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_68 z * u12 z = pow13_69_q z * f z + pow13_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_69_mul_integer z


theorem pow13_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_68 z * u12 z = pow13_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_69_mul z


theorem pow13_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 69 = pow13_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow13_68_pow z hz]
  exact pow13_69_root z hz


theorem pow13_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_69 z * pow13_69 z = pow13_138_q z * f z + pow13_138 z + (139 : R) * pow13_138_mul_t z := by
  simp only [pow13_69, pow13_138_q, f, pow13_138, pow13_138_mul_t]
  
  ring

theorem pow13_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_69 z * pow13_69 z = pow13_138_q z * f z + pow13_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_138_mul_integer z


theorem pow13_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_69 z * pow13_69 z = pow13_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_138_mul z


theorem pow13_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 138 = pow13_138 z := by
  calc
    _ = u12 z ^ 69 * u12 z ^ 69 := by ring
    _ = pow13_69 z * pow13_69 z := by rw [pow13_69_pow z hz]
    _ = _ := pow13_138_root z hz


theorem pow13_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_138 z * u12 z = pow13_139_q z * f z + pow13_139 z + (139 : R) * pow13_139_mul_t z := by
  simp only [pow13_138, u12, pow13_139_q, f, pow13_139, pow13_139_mul_t]
  simp only [pow12_139]
  ring

theorem pow13_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_138 z * u12 z = pow13_139_q z * f z + pow13_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_139_mul_integer z


theorem pow13_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_138 z * u12 z = pow13_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_139_mul z


theorem pow13_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 139 = pow13_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow13_138_pow z hz]
  exact pow13_139_root z hz


theorem iterate13 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 13) = u13 z := by
  calc
    _ = (z ^ (139 ^ 12)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u12 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate12 z hz)
    _ = _ := pow13_139_pow z hz


theorem pow14_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z + (139 : R) * pow14_2_mul_t z := by
  simp only [u13, pow14_2_q, f, pow14_2, pow14_2_mul_t]
  simp only [pow13_139]
  ring

theorem pow14_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_2_mul_integer z


theorem pow14_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z * u13 z = pow14_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_2_mul z


theorem pow14_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 2 = pow14_2 z := by
  calc
    _ = u13 z ^ 1 * u13 z ^ 1 := by ring
    _ = u13 z * u13 z := by simp only [pow_one]
    _ = _ := pow14_2_root z hz


theorem pow14_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z + (139 : R) * pow14_4_mul_t z := by
  simp only [pow14_2, pow14_4_q, f, pow14_4, pow14_4_mul_t]
  
  ring

theorem pow14_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_4_mul_integer z


theorem pow14_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_2 z * pow14_2 z = pow14_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_4_mul z


theorem pow14_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 4 = pow14_4 z := by
  calc
    _ = u13 z ^ 2 * u13 z ^ 2 := by ring
    _ = pow14_2 z * pow14_2 z := by rw [pow14_2_pow z hz]
    _ = _ := pow14_4_root z hz


theorem pow14_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_4 z * pow14_4 z = pow14_8_q z * f z + pow14_8 z + (139 : R) * pow14_8_mul_t z := by
  simp only [pow14_4, pow14_8_q, f, pow14_8, pow14_8_mul_t]
  
  ring

theorem pow14_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_4 z * pow14_4 z = pow14_8_q z * f z + pow14_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_8_mul_integer z


theorem pow14_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_4 z * pow14_4 z = pow14_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_8_mul z


theorem pow14_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 8 = pow14_8 z := by
  calc
    _ = u13 z ^ 4 * u13 z ^ 4 := by ring
    _ = pow14_4 z * pow14_4 z := by rw [pow14_4_pow z hz]
    _ = _ := pow14_8_root z hz


theorem pow14_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_8 z * pow14_8 z = pow14_16_q z * f z + pow14_16 z + (139 : R) * pow14_16_mul_t z := by
  simp only [pow14_8, pow14_16_q, f, pow14_16, pow14_16_mul_t]
  
  ring

theorem pow14_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_8 z * pow14_8 z = pow14_16_q z * f z + pow14_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_16_mul_integer z


theorem pow14_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_8 z * pow14_8 z = pow14_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_16_mul z


theorem pow14_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 16 = pow14_16 z := by
  calc
    _ = u13 z ^ 8 * u13 z ^ 8 := by ring
    _ = pow14_8 z * pow14_8 z := by rw [pow14_8_pow z hz]
    _ = _ := pow14_16_root z hz


theorem pow14_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_16 z * u13 z = pow14_17_q z * f z + pow14_17 z + (139 : R) * pow14_17_mul_t z := by
  simp only [pow14_16, u13, pow14_17_q, f, pow14_17, pow14_17_mul_t]
  simp only [pow13_139]
  ring

theorem pow14_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_16 z * u13 z = pow14_17_q z * f z + pow14_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_17_mul_integer z


theorem pow14_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_16 z * u13 z = pow14_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_17_mul z


theorem pow14_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 17 = pow14_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow14_16_pow z hz]
  exact pow14_17_root z hz


theorem pow14_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_17 z * pow14_17 z = pow14_34_q z * f z + pow14_34 z + (139 : R) * pow14_34_mul_t z := by
  simp only [pow14_17, pow14_34_q, f, pow14_34, pow14_34_mul_t]
  
  ring

theorem pow14_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_17 z * pow14_17 z = pow14_34_q z * f z + pow14_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_34_mul_integer z


theorem pow14_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_17 z * pow14_17 z = pow14_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_34_mul z


theorem pow14_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 34 = pow14_34 z := by
  calc
    _ = u13 z ^ 17 * u13 z ^ 17 := by ring
    _ = pow14_17 z * pow14_17 z := by rw [pow14_17_pow z hz]
    _ = _ := pow14_34_root z hz


theorem pow14_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_34 z * pow14_34 z = pow14_68_q z * f z + pow14_68 z + (139 : R) * pow14_68_mul_t z := by
  simp only [pow14_34, pow14_68_q, f, pow14_68, pow14_68_mul_t]
  
  ring

theorem pow14_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_34 z * pow14_34 z = pow14_68_q z * f z + pow14_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_68_mul_integer z


theorem pow14_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_34 z * pow14_34 z = pow14_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_68_mul z


theorem pow14_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 68 = pow14_68 z := by
  calc
    _ = u13 z ^ 34 * u13 z ^ 34 := by ring
    _ = pow14_34 z * pow14_34 z := by rw [pow14_34_pow z hz]
    _ = _ := pow14_68_root z hz


theorem pow14_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_68 z * u13 z = pow14_69_q z * f z + pow14_69 z + (139 : R) * pow14_69_mul_t z := by
  simp only [pow14_68, u13, pow14_69_q, f, pow14_69, pow14_69_mul_t]
  simp only [pow13_139]
  ring

theorem pow14_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_68 z * u13 z = pow14_69_q z * f z + pow14_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_69_mul_integer z


theorem pow14_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_68 z * u13 z = pow14_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_69_mul z


theorem pow14_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 69 = pow14_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow14_68_pow z hz]
  exact pow14_69_root z hz


theorem pow14_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_69 z * pow14_69 z = pow14_138_q z * f z + pow14_138 z + (139 : R) * pow14_138_mul_t z := by
  simp only [pow14_69, pow14_138_q, f, pow14_138, pow14_138_mul_t]
  
  ring

theorem pow14_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_69 z * pow14_69 z = pow14_138_q z * f z + pow14_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_138_mul_integer z


theorem pow14_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_69 z * pow14_69 z = pow14_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_138_mul z


theorem pow14_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 138 = pow14_138 z := by
  calc
    _ = u13 z ^ 69 * u13 z ^ 69 := by ring
    _ = pow14_69 z * pow14_69 z := by rw [pow14_69_pow z hz]
    _ = _ := pow14_138_root z hz


theorem pow14_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_138 z * u13 z = pow14_139_q z * f z + pow14_139 z + (139 : R) * pow14_139_mul_t z := by
  simp only [pow14_138, u13, pow14_139_q, f, pow14_139, pow14_139_mul_t]
  simp only [pow13_139]
  ring

theorem pow14_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_138 z * u13 z = pow14_139_q z * f z + pow14_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_139_mul_integer z


theorem pow14_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_138 z * u13 z = pow14_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_139_mul z


theorem pow14_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 139 = pow14_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow14_138_pow z hz]
  exact pow14_139_root z hz


theorem iterate14 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 14) = u14 z := by
  calc
    _ = (z ^ (139 ^ 13)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u13 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate13 z hz)
    _ = _ := pow14_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers08
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow15_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z + (139 : R) * pow15_2_mul_t z := by
  simp only [u14, pow15_2_q, f, pow15_2, pow15_2_mul_t]
  simp only [pow14_139]
  ring

theorem pow15_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_2_mul_integer z


theorem pow15_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z * u14 z = pow15_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_2_mul z


theorem pow15_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 2 = pow15_2 z := by
  calc
    _ = u14 z ^ 1 * u14 z ^ 1 := by ring
    _ = u14 z * u14 z := by simp only [pow_one]
    _ = _ := pow15_2_root z hz


theorem pow15_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z + (139 : R) * pow15_4_mul_t z := by
  simp only [pow15_2, pow15_4_q, f, pow15_4, pow15_4_mul_t]
  
  ring

theorem pow15_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_4_mul_integer z


theorem pow15_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_2 z * pow15_2 z = pow15_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_4_mul z


theorem pow15_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 4 = pow15_4 z := by
  calc
    _ = u14 z ^ 2 * u14 z ^ 2 := by ring
    _ = pow15_2 z * pow15_2 z := by rw [pow15_2_pow z hz]
    _ = _ := pow15_4_root z hz


theorem pow15_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_4 z * pow15_4 z = pow15_8_q z * f z + pow15_8 z + (139 : R) * pow15_8_mul_t z := by
  simp only [pow15_4, pow15_8_q, f, pow15_8, pow15_8_mul_t]
  
  ring

theorem pow15_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_4 z * pow15_4 z = pow15_8_q z * f z + pow15_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_8_mul_integer z


theorem pow15_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_4 z * pow15_4 z = pow15_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_8_mul z


theorem pow15_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 8 = pow15_8 z := by
  calc
    _ = u14 z ^ 4 * u14 z ^ 4 := by ring
    _ = pow15_4 z * pow15_4 z := by rw [pow15_4_pow z hz]
    _ = _ := pow15_8_root z hz


theorem pow15_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_8 z * pow15_8 z = pow15_16_q z * f z + pow15_16 z + (139 : R) * pow15_16_mul_t z := by
  simp only [pow15_8, pow15_16_q, f, pow15_16, pow15_16_mul_t]
  
  ring

theorem pow15_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_8 z * pow15_8 z = pow15_16_q z * f z + pow15_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_16_mul_integer z


theorem pow15_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_8 z * pow15_8 z = pow15_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_16_mul z


theorem pow15_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 16 = pow15_16 z := by
  calc
    _ = u14 z ^ 8 * u14 z ^ 8 := by ring
    _ = pow15_8 z * pow15_8 z := by rw [pow15_8_pow z hz]
    _ = _ := pow15_16_root z hz


theorem pow15_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_16 z * u14 z = pow15_17_q z * f z + pow15_17 z + (139 : R) * pow15_17_mul_t z := by
  simp only [pow15_16, u14, pow15_17_q, f, pow15_17, pow15_17_mul_t]
  simp only [pow14_139]
  ring

theorem pow15_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_16 z * u14 z = pow15_17_q z * f z + pow15_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_17_mul_integer z


theorem pow15_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_16 z * u14 z = pow15_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_17_mul z


theorem pow15_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 17 = pow15_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow15_16_pow z hz]
  exact pow15_17_root z hz


theorem pow15_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_17 z * pow15_17 z = pow15_34_q z * f z + pow15_34 z + (139 : R) * pow15_34_mul_t z := by
  simp only [pow15_17, pow15_34_q, f, pow15_34, pow15_34_mul_t]
  
  ring

theorem pow15_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_17 z * pow15_17 z = pow15_34_q z * f z + pow15_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_34_mul_integer z


theorem pow15_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_17 z * pow15_17 z = pow15_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_34_mul z


theorem pow15_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 34 = pow15_34 z := by
  calc
    _ = u14 z ^ 17 * u14 z ^ 17 := by ring
    _ = pow15_17 z * pow15_17 z := by rw [pow15_17_pow z hz]
    _ = _ := pow15_34_root z hz


theorem pow15_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_34 z * pow15_34 z = pow15_68_q z * f z + pow15_68 z + (139 : R) * pow15_68_mul_t z := by
  simp only [pow15_34, pow15_68_q, f, pow15_68, pow15_68_mul_t]
  
  ring

theorem pow15_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_34 z * pow15_34 z = pow15_68_q z * f z + pow15_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_68_mul_integer z


theorem pow15_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_34 z * pow15_34 z = pow15_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_68_mul z


theorem pow15_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 68 = pow15_68 z := by
  calc
    _ = u14 z ^ 34 * u14 z ^ 34 := by ring
    _ = pow15_34 z * pow15_34 z := by rw [pow15_34_pow z hz]
    _ = _ := pow15_68_root z hz


theorem pow15_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_68 z * u14 z = pow15_69_q z * f z + pow15_69 z + (139 : R) * pow15_69_mul_t z := by
  simp only [pow15_68, u14, pow15_69_q, f, pow15_69, pow15_69_mul_t]
  simp only [pow14_139]
  ring

theorem pow15_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_68 z * u14 z = pow15_69_q z * f z + pow15_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_69_mul_integer z


theorem pow15_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_68 z * u14 z = pow15_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_69_mul z


theorem pow15_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 69 = pow15_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow15_68_pow z hz]
  exact pow15_69_root z hz


theorem pow15_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_69 z * pow15_69 z = pow15_138_q z * f z + pow15_138 z + (139 : R) * pow15_138_mul_t z := by
  simp only [pow15_69, pow15_138_q, f, pow15_138, pow15_138_mul_t]
  
  ring

theorem pow15_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_69 z * pow15_69 z = pow15_138_q z * f z + pow15_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_138_mul_integer z


theorem pow15_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_69 z * pow15_69 z = pow15_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_138_mul z


theorem pow15_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 138 = pow15_138 z := by
  calc
    _ = u14 z ^ 69 * u14 z ^ 69 := by ring
    _ = pow15_69 z * pow15_69 z := by rw [pow15_69_pow z hz]
    _ = _ := pow15_138_root z hz


theorem pow15_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_138 z * u14 z = pow15_139_q z * f z + pow15_139 z + (139 : R) * pow15_139_mul_t z := by
  simp only [pow15_138, u14, pow15_139_q, f, pow15_139, pow15_139_mul_t]
  simp only [pow14_139]
  ring

theorem pow15_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_138 z * u14 z = pow15_139_q z * f z + pow15_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_139_mul_integer z


theorem pow15_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_138 z * u14 z = pow15_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_139_mul z


theorem pow15_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 139 = pow15_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow15_138_pow z hz]
  exact pow15_139_root z hz


theorem iterate15 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 15) = u15 z := by
  calc
    _ = (z ^ (139 ^ 14)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u14 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate14 z hz)
    _ = _ := pow15_139_pow z hz


theorem pow16_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z + (139 : R) * pow16_2_mul_t z := by
  simp only [u15, pow16_2_q, f, pow16_2, pow16_2_mul_t]
  simp only [pow15_139]
  ring

theorem pow16_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_2_mul_integer z


theorem pow16_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z * u15 z = pow16_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_2_mul z


theorem pow16_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 2 = pow16_2 z := by
  calc
    _ = u15 z ^ 1 * u15 z ^ 1 := by ring
    _ = u15 z * u15 z := by simp only [pow_one]
    _ = _ := pow16_2_root z hz


theorem pow16_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z + (139 : R) * pow16_4_mul_t z := by
  simp only [pow16_2, pow16_4_q, f, pow16_4, pow16_4_mul_t]
  
  ring

theorem pow16_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_4_mul_integer z


theorem pow16_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_2 z * pow16_2 z = pow16_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_4_mul z


theorem pow16_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 4 = pow16_4 z := by
  calc
    _ = u15 z ^ 2 * u15 z ^ 2 := by ring
    _ = pow16_2 z * pow16_2 z := by rw [pow16_2_pow z hz]
    _ = _ := pow16_4_root z hz


theorem pow16_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_4 z * pow16_4 z = pow16_8_q z * f z + pow16_8 z + (139 : R) * pow16_8_mul_t z := by
  simp only [pow16_4, pow16_8_q, f, pow16_8, pow16_8_mul_t]
  
  ring

theorem pow16_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_4 z * pow16_4 z = pow16_8_q z * f z + pow16_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_8_mul_integer z


theorem pow16_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_4 z * pow16_4 z = pow16_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_8_mul z


theorem pow16_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 8 = pow16_8 z := by
  calc
    _ = u15 z ^ 4 * u15 z ^ 4 := by ring
    _ = pow16_4 z * pow16_4 z := by rw [pow16_4_pow z hz]
    _ = _ := pow16_8_root z hz


theorem pow16_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_8 z * pow16_8 z = pow16_16_q z * f z + pow16_16 z + (139 : R) * pow16_16_mul_t z := by
  simp only [pow16_8, pow16_16_q, f, pow16_16, pow16_16_mul_t]
  
  ring

theorem pow16_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_8 z * pow16_8 z = pow16_16_q z * f z + pow16_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_16_mul_integer z


theorem pow16_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_8 z * pow16_8 z = pow16_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_16_mul z


theorem pow16_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 16 = pow16_16 z := by
  calc
    _ = u15 z ^ 8 * u15 z ^ 8 := by ring
    _ = pow16_8 z * pow16_8 z := by rw [pow16_8_pow z hz]
    _ = _ := pow16_16_root z hz


theorem pow16_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_16 z * u15 z = pow16_17_q z * f z + pow16_17 z + (139 : R) * pow16_17_mul_t z := by
  simp only [pow16_16, u15, pow16_17_q, f, pow16_17, pow16_17_mul_t]
  simp only [pow15_139]
  ring

theorem pow16_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_16 z * u15 z = pow16_17_q z * f z + pow16_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_17_mul_integer z


theorem pow16_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_16 z * u15 z = pow16_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_17_mul z


theorem pow16_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 17 = pow16_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow16_16_pow z hz]
  exact pow16_17_root z hz


theorem pow16_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_17 z * pow16_17 z = pow16_34_q z * f z + pow16_34 z + (139 : R) * pow16_34_mul_t z := by
  simp only [pow16_17, pow16_34_q, f, pow16_34, pow16_34_mul_t]
  
  ring

theorem pow16_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_17 z * pow16_17 z = pow16_34_q z * f z + pow16_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_34_mul_integer z


theorem pow16_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_17 z * pow16_17 z = pow16_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_34_mul z


theorem pow16_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 34 = pow16_34 z := by
  calc
    _ = u15 z ^ 17 * u15 z ^ 17 := by ring
    _ = pow16_17 z * pow16_17 z := by rw [pow16_17_pow z hz]
    _ = _ := pow16_34_root z hz


theorem pow16_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_34 z * pow16_34 z = pow16_68_q z * f z + pow16_68 z + (139 : R) * pow16_68_mul_t z := by
  simp only [pow16_34, pow16_68_q, f, pow16_68, pow16_68_mul_t]
  
  ring

theorem pow16_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_34 z * pow16_34 z = pow16_68_q z * f z + pow16_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_68_mul_integer z


theorem pow16_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_34 z * pow16_34 z = pow16_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_68_mul z


theorem pow16_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 68 = pow16_68 z := by
  calc
    _ = u15 z ^ 34 * u15 z ^ 34 := by ring
    _ = pow16_34 z * pow16_34 z := by rw [pow16_34_pow z hz]
    _ = _ := pow16_68_root z hz


theorem pow16_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_68 z * u15 z = pow16_69_q z * f z + pow16_69 z + (139 : R) * pow16_69_mul_t z := by
  simp only [pow16_68, u15, pow16_69_q, f, pow16_69, pow16_69_mul_t]
  simp only [pow15_139]
  ring

theorem pow16_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_68 z * u15 z = pow16_69_q z * f z + pow16_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_69_mul_integer z


theorem pow16_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_68 z * u15 z = pow16_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_69_mul z


theorem pow16_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 69 = pow16_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow16_68_pow z hz]
  exact pow16_69_root z hz


theorem pow16_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_69 z * pow16_69 z = pow16_138_q z * f z + pow16_138 z + (139 : R) * pow16_138_mul_t z := by
  simp only [pow16_69, pow16_138_q, f, pow16_138, pow16_138_mul_t]
  
  ring

theorem pow16_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_69 z * pow16_69 z = pow16_138_q z * f z + pow16_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_138_mul_integer z


theorem pow16_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_69 z * pow16_69 z = pow16_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_138_mul z


theorem pow16_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 138 = pow16_138 z := by
  calc
    _ = u15 z ^ 69 * u15 z ^ 69 := by ring
    _ = pow16_69 z * pow16_69 z := by rw [pow16_69_pow z hz]
    _ = _ := pow16_138_root z hz


theorem pow16_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_138 z * u15 z = pow16_139_q z * f z + pow16_139 z + (139 : R) * pow16_139_mul_t z := by
  simp only [pow16_138, u15, pow16_139_q, f, pow16_139, pow16_139_mul_t]
  simp only [pow15_139]
  ring

theorem pow16_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_138 z * u15 z = pow16_139_q z * f z + pow16_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_139_mul_integer z


theorem pow16_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_138 z * u15 z = pow16_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_139_mul z


theorem pow16_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 139 = pow16_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow16_138_pow z hz]
  exact pow16_139_root z hz


theorem iterate16 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 16) = u16 z := by
  calc
    _ = (z ^ (139 ^ 15)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u15 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate15 z hz)
    _ = _ := pow16_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers09
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow17_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z + (139 : R) * pow17_2_mul_t z := by
  simp only [u16, pow17_2_q, f, pow17_2, pow17_2_mul_t]
  simp only [pow16_139]
  ring

theorem pow17_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_2_mul_integer z


theorem pow17_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z * u16 z = pow17_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_2_mul z


theorem pow17_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 2 = pow17_2 z := by
  calc
    _ = u16 z ^ 1 * u16 z ^ 1 := by ring
    _ = u16 z * u16 z := by simp only [pow_one]
    _ = _ := pow17_2_root z hz


theorem pow17_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z + (139 : R) * pow17_4_mul_t z := by
  simp only [pow17_2, pow17_4_q, f, pow17_4, pow17_4_mul_t]
  
  ring

theorem pow17_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_4_mul_integer z


theorem pow17_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_2 z * pow17_2 z = pow17_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_4_mul z


theorem pow17_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 4 = pow17_4 z := by
  calc
    _ = u16 z ^ 2 * u16 z ^ 2 := by ring
    _ = pow17_2 z * pow17_2 z := by rw [pow17_2_pow z hz]
    _ = _ := pow17_4_root z hz


theorem pow17_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_4 z * pow17_4 z = pow17_8_q z * f z + pow17_8 z + (139 : R) * pow17_8_mul_t z := by
  simp only [pow17_4, pow17_8_q, f, pow17_8, pow17_8_mul_t]
  
  ring

theorem pow17_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_4 z * pow17_4 z = pow17_8_q z * f z + pow17_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_8_mul_integer z


theorem pow17_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_4 z * pow17_4 z = pow17_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_8_mul z


theorem pow17_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 8 = pow17_8 z := by
  calc
    _ = u16 z ^ 4 * u16 z ^ 4 := by ring
    _ = pow17_4 z * pow17_4 z := by rw [pow17_4_pow z hz]
    _ = _ := pow17_8_root z hz


theorem pow17_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_8 z * pow17_8 z = pow17_16_q z * f z + pow17_16 z + (139 : R) * pow17_16_mul_t z := by
  simp only [pow17_8, pow17_16_q, f, pow17_16, pow17_16_mul_t]
  
  ring

theorem pow17_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_8 z * pow17_8 z = pow17_16_q z * f z + pow17_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_16_mul_integer z


theorem pow17_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_8 z * pow17_8 z = pow17_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_16_mul z


theorem pow17_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 16 = pow17_16 z := by
  calc
    _ = u16 z ^ 8 * u16 z ^ 8 := by ring
    _ = pow17_8 z * pow17_8 z := by rw [pow17_8_pow z hz]
    _ = _ := pow17_16_root z hz


theorem pow17_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_16 z * u16 z = pow17_17_q z * f z + pow17_17 z + (139 : R) * pow17_17_mul_t z := by
  simp only [pow17_16, u16, pow17_17_q, f, pow17_17, pow17_17_mul_t]
  simp only [pow16_139]
  ring

theorem pow17_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_16 z * u16 z = pow17_17_q z * f z + pow17_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_17_mul_integer z


theorem pow17_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_16 z * u16 z = pow17_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_17_mul z


theorem pow17_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 17 = pow17_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow17_16_pow z hz]
  exact pow17_17_root z hz


theorem pow17_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_17 z * pow17_17 z = pow17_34_q z * f z + pow17_34 z + (139 : R) * pow17_34_mul_t z := by
  simp only [pow17_17, pow17_34_q, f, pow17_34, pow17_34_mul_t]
  
  ring

theorem pow17_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_17 z * pow17_17 z = pow17_34_q z * f z + pow17_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_34_mul_integer z


theorem pow17_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_17 z * pow17_17 z = pow17_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_34_mul z


theorem pow17_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 34 = pow17_34 z := by
  calc
    _ = u16 z ^ 17 * u16 z ^ 17 := by ring
    _ = pow17_17 z * pow17_17 z := by rw [pow17_17_pow z hz]
    _ = _ := pow17_34_root z hz


theorem pow17_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_34 z * pow17_34 z = pow17_68_q z * f z + pow17_68 z + (139 : R) * pow17_68_mul_t z := by
  simp only [pow17_34, pow17_68_q, f, pow17_68, pow17_68_mul_t]
  
  ring

theorem pow17_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_34 z * pow17_34 z = pow17_68_q z * f z + pow17_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_68_mul_integer z


theorem pow17_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_34 z * pow17_34 z = pow17_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_68_mul z


theorem pow17_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 68 = pow17_68 z := by
  calc
    _ = u16 z ^ 34 * u16 z ^ 34 := by ring
    _ = pow17_34 z * pow17_34 z := by rw [pow17_34_pow z hz]
    _ = _ := pow17_68_root z hz


theorem pow17_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_68 z * u16 z = pow17_69_q z * f z + pow17_69 z + (139 : R) * pow17_69_mul_t z := by
  simp only [pow17_68, u16, pow17_69_q, f, pow17_69, pow17_69_mul_t]
  simp only [pow16_139]
  ring

theorem pow17_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_68 z * u16 z = pow17_69_q z * f z + pow17_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_69_mul_integer z


theorem pow17_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_68 z * u16 z = pow17_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_69_mul z


theorem pow17_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 69 = pow17_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow17_68_pow z hz]
  exact pow17_69_root z hz


theorem pow17_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_69 z * pow17_69 z = pow17_138_q z * f z + pow17_138 z + (139 : R) * pow17_138_mul_t z := by
  simp only [pow17_69, pow17_138_q, f, pow17_138, pow17_138_mul_t]
  
  ring

theorem pow17_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_69 z * pow17_69 z = pow17_138_q z * f z + pow17_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_138_mul_integer z


theorem pow17_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_69 z * pow17_69 z = pow17_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_138_mul z


theorem pow17_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 138 = pow17_138 z := by
  calc
    _ = u16 z ^ 69 * u16 z ^ 69 := by ring
    _ = pow17_69 z * pow17_69 z := by rw [pow17_69_pow z hz]
    _ = _ := pow17_138_root z hz


theorem pow17_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_138 z * u16 z = pow17_139_q z * f z + pow17_139 z + (139 : R) * pow17_139_mul_t z := by
  simp only [pow17_138, u16, pow17_139_q, f, pow17_139, pow17_139_mul_t]
  simp only [pow16_139]
  ring

theorem pow17_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_138 z * u16 z = pow17_139_q z * f z + pow17_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_139_mul_integer z


theorem pow17_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_138 z * u16 z = pow17_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_139_mul z


theorem pow17_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 139 = pow17_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow17_138_pow z hz]
  exact pow17_139_root z hz


theorem iterate17 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 17) = u17 z := by
  calc
    _ = (z ^ (139 ^ 16)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u16 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate16 z hz)
    _ = _ := pow17_139_pow z hz


theorem pow18_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u17 z * u17 z = pow18_2_q z * f z + pow18_2 z + (139 : R) * pow18_2_mul_t z := by
  simp only [u17, pow18_2_q, f, pow18_2, pow18_2_mul_t]
  simp only [pow17_139]
  ring

theorem pow18_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u17 z * u17 z = pow18_2_q z * f z + pow18_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_2_mul_integer z


theorem pow18_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z * u17 z = pow18_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_2_mul z


theorem pow18_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 2 = pow18_2 z := by
  calc
    _ = u17 z ^ 1 * u17 z ^ 1 := by ring
    _ = u17 z * u17 z := by simp only [pow_one]
    _ = _ := pow18_2_root z hz


theorem pow18_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_2 z * pow18_2 z = pow18_4_q z * f z + pow18_4 z + (139 : R) * pow18_4_mul_t z := by
  simp only [pow18_2, pow18_4_q, f, pow18_4, pow18_4_mul_t]
  
  ring

theorem pow18_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_2 z * pow18_2 z = pow18_4_q z * f z + pow18_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_4_mul_integer z


theorem pow18_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_2 z * pow18_2 z = pow18_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_4_mul z


theorem pow18_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 4 = pow18_4 z := by
  calc
    _ = u17 z ^ 2 * u17 z ^ 2 := by ring
    _ = pow18_2 z * pow18_2 z := by rw [pow18_2_pow z hz]
    _ = _ := pow18_4_root z hz


theorem pow18_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_4 z * pow18_4 z = pow18_8_q z * f z + pow18_8 z + (139 : R) * pow18_8_mul_t z := by
  simp only [pow18_4, pow18_8_q, f, pow18_8, pow18_8_mul_t]
  
  ring

theorem pow18_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_4 z * pow18_4 z = pow18_8_q z * f z + pow18_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_8_mul_integer z


theorem pow18_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_4 z * pow18_4 z = pow18_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_8_mul z


theorem pow18_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 8 = pow18_8 z := by
  calc
    _ = u17 z ^ 4 * u17 z ^ 4 := by ring
    _ = pow18_4 z * pow18_4 z := by rw [pow18_4_pow z hz]
    _ = _ := pow18_8_root z hz


theorem pow18_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_8 z * pow18_8 z = pow18_16_q z * f z + pow18_16 z + (139 : R) * pow18_16_mul_t z := by
  simp only [pow18_8, pow18_16_q, f, pow18_16, pow18_16_mul_t]
  
  ring

theorem pow18_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_8 z * pow18_8 z = pow18_16_q z * f z + pow18_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_16_mul_integer z


theorem pow18_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_8 z * pow18_8 z = pow18_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_16_mul z


theorem pow18_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 16 = pow18_16 z := by
  calc
    _ = u17 z ^ 8 * u17 z ^ 8 := by ring
    _ = pow18_8 z * pow18_8 z := by rw [pow18_8_pow z hz]
    _ = _ := pow18_16_root z hz


theorem pow18_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_16 z * u17 z = pow18_17_q z * f z + pow18_17 z + (139 : R) * pow18_17_mul_t z := by
  simp only [pow18_16, u17, pow18_17_q, f, pow18_17, pow18_17_mul_t]
  simp only [pow17_139]
  ring

theorem pow18_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_16 z * u17 z = pow18_17_q z * f z + pow18_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_17_mul_integer z


theorem pow18_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_16 z * u17 z = pow18_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_17_mul z


theorem pow18_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 17 = pow18_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow18_16_pow z hz]
  exact pow18_17_root z hz


theorem pow18_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_17 z * pow18_17 z = pow18_34_q z * f z + pow18_34 z + (139 : R) * pow18_34_mul_t z := by
  simp only [pow18_17, pow18_34_q, f, pow18_34, pow18_34_mul_t]
  
  ring

theorem pow18_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_17 z * pow18_17 z = pow18_34_q z * f z + pow18_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_34_mul_integer z


theorem pow18_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_17 z * pow18_17 z = pow18_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_34_mul z


theorem pow18_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 34 = pow18_34 z := by
  calc
    _ = u17 z ^ 17 * u17 z ^ 17 := by ring
    _ = pow18_17 z * pow18_17 z := by rw [pow18_17_pow z hz]
    _ = _ := pow18_34_root z hz


theorem pow18_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_34 z * pow18_34 z = pow18_68_q z * f z + pow18_68 z + (139 : R) * pow18_68_mul_t z := by
  simp only [pow18_34, pow18_68_q, f, pow18_68, pow18_68_mul_t]
  
  ring

theorem pow18_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_34 z * pow18_34 z = pow18_68_q z * f z + pow18_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_68_mul_integer z


theorem pow18_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_34 z * pow18_34 z = pow18_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_68_mul z


theorem pow18_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 68 = pow18_68 z := by
  calc
    _ = u17 z ^ 34 * u17 z ^ 34 := by ring
    _ = pow18_34 z * pow18_34 z := by rw [pow18_34_pow z hz]
    _ = _ := pow18_68_root z hz


theorem pow18_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_68 z * u17 z = pow18_69_q z * f z + pow18_69 z + (139 : R) * pow18_69_mul_t z := by
  simp only [pow18_68, u17, pow18_69_q, f, pow18_69, pow18_69_mul_t]
  simp only [pow17_139]
  ring

theorem pow18_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_68 z * u17 z = pow18_69_q z * f z + pow18_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_69_mul_integer z


theorem pow18_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_68 z * u17 z = pow18_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_69_mul z


theorem pow18_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 69 = pow18_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow18_68_pow z hz]
  exact pow18_69_root z hz


theorem pow18_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_69 z * pow18_69 z = pow18_138_q z * f z + pow18_138 z + (139 : R) * pow18_138_mul_t z := by
  simp only [pow18_69, pow18_138_q, f, pow18_138, pow18_138_mul_t]
  
  ring

theorem pow18_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_69 z * pow18_69 z = pow18_138_q z * f z + pow18_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_138_mul_integer z


theorem pow18_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_69 z * pow18_69 z = pow18_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_138_mul z


theorem pow18_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 138 = pow18_138 z := by
  calc
    _ = u17 z ^ 69 * u17 z ^ 69 := by ring
    _ = pow18_69 z * pow18_69 z := by rw [pow18_69_pow z hz]
    _ = _ := pow18_138_root z hz


theorem pow18_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_138 z * u17 z = pow18_139_q z * f z + pow18_139 z + (139 : R) * pow18_139_mul_t z := by
  simp only [pow18_138, u17, pow18_139_q, f, pow18_139, pow18_139_mul_t]
  simp only [pow17_139]
  ring

theorem pow18_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_138 z * u17 z = pow18_139_q z * f z + pow18_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_139_mul_integer z


theorem pow18_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_138 z * u17 z = pow18_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_139_mul z


theorem pow18_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 139 = pow18_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow18_138_pow z hz]
  exact pow18_139_root z hz


theorem iterate18_oai {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 18) = u18 z := by
  calc
    _ = (z ^ (139 ^ 17)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u17 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate17 z hz)
    _ = _ := pow18_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Mod139.iterate18_oai.{u_1} := @OAI.DimensionTen.Mod139.iterate18_oai.{u_1}
