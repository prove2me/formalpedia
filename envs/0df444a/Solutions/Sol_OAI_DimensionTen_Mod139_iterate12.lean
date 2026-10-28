-- Prove2me | solution 1 for OAI.DimensionTen.Mod139.iterate12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:16:40.694608+00:00
-- url     : https://prove2.me/submissions/06117cd0-d666-45b4-9097-91cc1adb4f25

import Mathlib
import Definitions.Def_OAIQ033D009
import Definitions.Def_OAIQ033D013
import Theorems.Thm_OAI_DimensionTen_Mod139_iterate6

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers04
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow7_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z + (139 : R) * pow7_2_mul_t z := by
  simp only [u6, pow7_2_q, f, pow7_2, pow7_2_mul_t]
  simp only [pow6_139]
  ring

theorem pow7_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_2_mul_integer z


theorem pow7_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z * u6 z = pow7_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_2_mul z


theorem pow7_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 2 = pow7_2 z := by
  calc
    _ = u6 z ^ 1 * u6 z ^ 1 := by ring
    _ = u6 z * u6 z := by simp only [pow_one]
    _ = _ := pow7_2_root z hz


theorem pow7_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z + (139 : R) * pow7_4_mul_t z := by
  simp only [pow7_2, pow7_4_q, f, pow7_4, pow7_4_mul_t]
  
  ring

theorem pow7_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_4_mul_integer z


theorem pow7_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_2 z * pow7_2 z = pow7_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_4_mul z


theorem pow7_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 4 = pow7_4 z := by
  calc
    _ = u6 z ^ 2 * u6 z ^ 2 := by ring
    _ = pow7_2 z * pow7_2 z := by rw [pow7_2_pow z hz]
    _ = _ := pow7_4_root z hz


theorem pow7_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_4 z * pow7_4 z = pow7_8_q z * f z + pow7_8 z + (139 : R) * pow7_8_mul_t z := by
  simp only [pow7_4, pow7_8_q, f, pow7_8, pow7_8_mul_t]
  
  ring

theorem pow7_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_4 z * pow7_4 z = pow7_8_q z * f z + pow7_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_8_mul_integer z


theorem pow7_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_4 z * pow7_4 z = pow7_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_8_mul z


theorem pow7_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 8 = pow7_8 z := by
  calc
    _ = u6 z ^ 4 * u6 z ^ 4 := by ring
    _ = pow7_4 z * pow7_4 z := by rw [pow7_4_pow z hz]
    _ = _ := pow7_8_root z hz


theorem pow7_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_8 z * pow7_8 z = pow7_16_q z * f z + pow7_16 z + (139 : R) * pow7_16_mul_t z := by
  simp only [pow7_8, pow7_16_q, f, pow7_16, pow7_16_mul_t]
  
  ring

theorem pow7_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_8 z * pow7_8 z = pow7_16_q z * f z + pow7_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_16_mul_integer z


theorem pow7_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_8 z * pow7_8 z = pow7_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_16_mul z


theorem pow7_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 16 = pow7_16 z := by
  calc
    _ = u6 z ^ 8 * u6 z ^ 8 := by ring
    _ = pow7_8 z * pow7_8 z := by rw [pow7_8_pow z hz]
    _ = _ := pow7_16_root z hz


theorem pow7_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_16 z * u6 z = pow7_17_q z * f z + pow7_17 z + (139 : R) * pow7_17_mul_t z := by
  simp only [pow7_16, u6, pow7_17_q, f, pow7_17, pow7_17_mul_t]
  simp only [pow6_139]
  ring

theorem pow7_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_16 z * u6 z = pow7_17_q z * f z + pow7_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_17_mul_integer z


theorem pow7_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_16 z * u6 z = pow7_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_17_mul z


theorem pow7_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 17 = pow7_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow7_16_pow z hz]
  exact pow7_17_root z hz


theorem pow7_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_17 z * pow7_17 z = pow7_34_q z * f z + pow7_34 z + (139 : R) * pow7_34_mul_t z := by
  simp only [pow7_17, pow7_34_q, f, pow7_34, pow7_34_mul_t]
  
  ring

theorem pow7_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_17 z * pow7_17 z = pow7_34_q z * f z + pow7_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_34_mul_integer z


theorem pow7_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_17 z * pow7_17 z = pow7_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_34_mul z


theorem pow7_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 34 = pow7_34 z := by
  calc
    _ = u6 z ^ 17 * u6 z ^ 17 := by ring
    _ = pow7_17 z * pow7_17 z := by rw [pow7_17_pow z hz]
    _ = _ := pow7_34_root z hz


theorem pow7_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_34 z * pow7_34 z = pow7_68_q z * f z + pow7_68 z + (139 : R) * pow7_68_mul_t z := by
  simp only [pow7_34, pow7_68_q, f, pow7_68, pow7_68_mul_t]
  
  ring

theorem pow7_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_34 z * pow7_34 z = pow7_68_q z * f z + pow7_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_68_mul_integer z


theorem pow7_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_34 z * pow7_34 z = pow7_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_68_mul z


theorem pow7_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 68 = pow7_68 z := by
  calc
    _ = u6 z ^ 34 * u6 z ^ 34 := by ring
    _ = pow7_34 z * pow7_34 z := by rw [pow7_34_pow z hz]
    _ = _ := pow7_68_root z hz


theorem pow7_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_68 z * u6 z = pow7_69_q z * f z + pow7_69 z + (139 : R) * pow7_69_mul_t z := by
  simp only [pow7_68, u6, pow7_69_q, f, pow7_69, pow7_69_mul_t]
  simp only [pow6_139]
  ring

theorem pow7_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_68 z * u6 z = pow7_69_q z * f z + pow7_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_69_mul_integer z


theorem pow7_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_68 z * u6 z = pow7_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_69_mul z


theorem pow7_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 69 = pow7_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow7_68_pow z hz]
  exact pow7_69_root z hz


theorem pow7_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_69 z * pow7_69 z = pow7_138_q z * f z + pow7_138 z + (139 : R) * pow7_138_mul_t z := by
  simp only [pow7_69, pow7_138_q, f, pow7_138, pow7_138_mul_t]
  
  ring

theorem pow7_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_69 z * pow7_69 z = pow7_138_q z * f z + pow7_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_138_mul_integer z


theorem pow7_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_69 z * pow7_69 z = pow7_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_138_mul z


theorem pow7_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 138 = pow7_138 z := by
  calc
    _ = u6 z ^ 69 * u6 z ^ 69 := by ring
    _ = pow7_69 z * pow7_69 z := by rw [pow7_69_pow z hz]
    _ = _ := pow7_138_root z hz


theorem pow7_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_138 z * u6 z = pow7_139_q z * f z + pow7_139 z + (139 : R) * pow7_139_mul_t z := by
  simp only [pow7_138, u6, pow7_139_q, f, pow7_139, pow7_139_mul_t]
  simp only [pow6_139]
  ring

theorem pow7_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_138 z * u6 z = pow7_139_q z * f z + pow7_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_139_mul_integer z


theorem pow7_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_138 z * u6 z = pow7_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_139_mul z


theorem pow7_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 139 = pow7_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow7_138_pow z hz]
  exact pow7_139_root z hz


theorem iterate7 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 7) = u7 z := by
  calc
    _ = (z ^ (139 ^ 6)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u6 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate6 z hz)
    _ = _ := pow7_139_pow z hz


theorem pow8_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z + (139 : R) * pow8_2_mul_t z := by
  simp only [u7, pow8_2_q, f, pow8_2, pow8_2_mul_t]
  simp only [pow7_139]
  ring

theorem pow8_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_2_mul_integer z


theorem pow8_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z * u7 z = pow8_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_2_mul z


theorem pow8_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 2 = pow8_2 z := by
  calc
    _ = u7 z ^ 1 * u7 z ^ 1 := by ring
    _ = u7 z * u7 z := by simp only [pow_one]
    _ = _ := pow8_2_root z hz


theorem pow8_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z + (139 : R) * pow8_4_mul_t z := by
  simp only [pow8_2, pow8_4_q, f, pow8_4, pow8_4_mul_t]
  
  ring

theorem pow8_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_4_mul_integer z


theorem pow8_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_2 z * pow8_2 z = pow8_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_4_mul z


theorem pow8_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 4 = pow8_4 z := by
  calc
    _ = u7 z ^ 2 * u7 z ^ 2 := by ring
    _ = pow8_2 z * pow8_2 z := by rw [pow8_2_pow z hz]
    _ = _ := pow8_4_root z hz


theorem pow8_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_4 z * pow8_4 z = pow8_8_q z * f z + pow8_8 z + (139 : R) * pow8_8_mul_t z := by
  simp only [pow8_4, pow8_8_q, f, pow8_8, pow8_8_mul_t]
  
  ring

theorem pow8_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_4 z * pow8_4 z = pow8_8_q z * f z + pow8_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_8_mul_integer z


theorem pow8_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_4 z * pow8_4 z = pow8_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_8_mul z


theorem pow8_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 8 = pow8_8 z := by
  calc
    _ = u7 z ^ 4 * u7 z ^ 4 := by ring
    _ = pow8_4 z * pow8_4 z := by rw [pow8_4_pow z hz]
    _ = _ := pow8_8_root z hz


theorem pow8_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_8 z * pow8_8 z = pow8_16_q z * f z + pow8_16 z + (139 : R) * pow8_16_mul_t z := by
  simp only [pow8_8, pow8_16_q, f, pow8_16, pow8_16_mul_t]
  
  ring

theorem pow8_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_8 z * pow8_8 z = pow8_16_q z * f z + pow8_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_16_mul_integer z


theorem pow8_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_8 z * pow8_8 z = pow8_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_16_mul z


theorem pow8_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 16 = pow8_16 z := by
  calc
    _ = u7 z ^ 8 * u7 z ^ 8 := by ring
    _ = pow8_8 z * pow8_8 z := by rw [pow8_8_pow z hz]
    _ = _ := pow8_16_root z hz


theorem pow8_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_16 z * u7 z = pow8_17_q z * f z + pow8_17 z + (139 : R) * pow8_17_mul_t z := by
  simp only [pow8_16, u7, pow8_17_q, f, pow8_17, pow8_17_mul_t]
  simp only [pow7_139]
  ring

theorem pow8_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_16 z * u7 z = pow8_17_q z * f z + pow8_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_17_mul_integer z


theorem pow8_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_16 z * u7 z = pow8_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_17_mul z


theorem pow8_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 17 = pow8_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow8_16_pow z hz]
  exact pow8_17_root z hz


theorem pow8_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_17 z * pow8_17 z = pow8_34_q z * f z + pow8_34 z + (139 : R) * pow8_34_mul_t z := by
  simp only [pow8_17, pow8_34_q, f, pow8_34, pow8_34_mul_t]
  
  ring

theorem pow8_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_17 z * pow8_17 z = pow8_34_q z * f z + pow8_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_34_mul_integer z


theorem pow8_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_17 z * pow8_17 z = pow8_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_34_mul z


theorem pow8_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 34 = pow8_34 z := by
  calc
    _ = u7 z ^ 17 * u7 z ^ 17 := by ring
    _ = pow8_17 z * pow8_17 z := by rw [pow8_17_pow z hz]
    _ = _ := pow8_34_root z hz


theorem pow8_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_34 z * pow8_34 z = pow8_68_q z * f z + pow8_68 z + (139 : R) * pow8_68_mul_t z := by
  simp only [pow8_34, pow8_68_q, f, pow8_68, pow8_68_mul_t]
  
  ring

theorem pow8_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_34 z * pow8_34 z = pow8_68_q z * f z + pow8_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_68_mul_integer z


theorem pow8_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_34 z * pow8_34 z = pow8_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_68_mul z


theorem pow8_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 68 = pow8_68 z := by
  calc
    _ = u7 z ^ 34 * u7 z ^ 34 := by ring
    _ = pow8_34 z * pow8_34 z := by rw [pow8_34_pow z hz]
    _ = _ := pow8_68_root z hz


theorem pow8_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_68 z * u7 z = pow8_69_q z * f z + pow8_69 z + (139 : R) * pow8_69_mul_t z := by
  simp only [pow8_68, u7, pow8_69_q, f, pow8_69, pow8_69_mul_t]
  simp only [pow7_139]
  ring

theorem pow8_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_68 z * u7 z = pow8_69_q z * f z + pow8_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_69_mul_integer z


theorem pow8_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_68 z * u7 z = pow8_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_69_mul z


theorem pow8_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 69 = pow8_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow8_68_pow z hz]
  exact pow8_69_root z hz


theorem pow8_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_69 z * pow8_69 z = pow8_138_q z * f z + pow8_138 z + (139 : R) * pow8_138_mul_t z := by
  simp only [pow8_69, pow8_138_q, f, pow8_138, pow8_138_mul_t]
  
  ring

theorem pow8_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_69 z * pow8_69 z = pow8_138_q z * f z + pow8_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_138_mul_integer z


theorem pow8_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_69 z * pow8_69 z = pow8_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_138_mul z


theorem pow8_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 138 = pow8_138 z := by
  calc
    _ = u7 z ^ 69 * u7 z ^ 69 := by ring
    _ = pow8_69 z * pow8_69 z := by rw [pow8_69_pow z hz]
    _ = _ := pow8_138_root z hz


theorem pow8_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_138 z * u7 z = pow8_139_q z * f z + pow8_139 z + (139 : R) * pow8_139_mul_t z := by
  simp only [pow8_138, u7, pow8_139_q, f, pow8_139, pow8_139_mul_t]
  simp only [pow7_139]
  ring

theorem pow8_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_138 z * u7 z = pow8_139_q z * f z + pow8_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_139_mul_integer z


theorem pow8_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_138 z * u7 z = pow8_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_139_mul z


theorem pow8_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 139 = pow8_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow8_138_pow z hz]
  exact pow8_139_root z hz


theorem iterate8 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 8) = u8 z := by
  calc
    _ = (z ^ (139 ^ 7)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u7 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate7 z hz)
    _ = _ := pow8_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers05
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow9_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z + (139 : R) * pow9_2_mul_t z := by
  simp only [u8, pow9_2_q, f, pow9_2, pow9_2_mul_t]
  simp only [pow8_139]
  ring

theorem pow9_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_2_mul_integer z


theorem pow9_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z * u8 z = pow9_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_2_mul z


theorem pow9_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 2 = pow9_2 z := by
  calc
    _ = u8 z ^ 1 * u8 z ^ 1 := by ring
    _ = u8 z * u8 z := by simp only [pow_one]
    _ = _ := pow9_2_root z hz


theorem pow9_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z + (139 : R) * pow9_4_mul_t z := by
  simp only [pow9_2, pow9_4_q, f, pow9_4, pow9_4_mul_t]
  
  ring

theorem pow9_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_4_mul_integer z


theorem pow9_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_2 z * pow9_2 z = pow9_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_4_mul z


theorem pow9_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 4 = pow9_4 z := by
  calc
    _ = u8 z ^ 2 * u8 z ^ 2 := by ring
    _ = pow9_2 z * pow9_2 z := by rw [pow9_2_pow z hz]
    _ = _ := pow9_4_root z hz


theorem pow9_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_4 z * pow9_4 z = pow9_8_q z * f z + pow9_8 z + (139 : R) * pow9_8_mul_t z := by
  simp only [pow9_4, pow9_8_q, f, pow9_8, pow9_8_mul_t]
  
  ring

theorem pow9_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_4 z * pow9_4 z = pow9_8_q z * f z + pow9_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_8_mul_integer z


theorem pow9_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_4 z * pow9_4 z = pow9_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_8_mul z


theorem pow9_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 8 = pow9_8 z := by
  calc
    _ = u8 z ^ 4 * u8 z ^ 4 := by ring
    _ = pow9_4 z * pow9_4 z := by rw [pow9_4_pow z hz]
    _ = _ := pow9_8_root z hz


theorem pow9_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_8 z * pow9_8 z = pow9_16_q z * f z + pow9_16 z + (139 : R) * pow9_16_mul_t z := by
  simp only [pow9_8, pow9_16_q, f, pow9_16, pow9_16_mul_t]
  
  ring

theorem pow9_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_8 z * pow9_8 z = pow9_16_q z * f z + pow9_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_16_mul_integer z


theorem pow9_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_8 z * pow9_8 z = pow9_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_16_mul z


theorem pow9_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 16 = pow9_16 z := by
  calc
    _ = u8 z ^ 8 * u8 z ^ 8 := by ring
    _ = pow9_8 z * pow9_8 z := by rw [pow9_8_pow z hz]
    _ = _ := pow9_16_root z hz


theorem pow9_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_16 z * u8 z = pow9_17_q z * f z + pow9_17 z + (139 : R) * pow9_17_mul_t z := by
  simp only [pow9_16, u8, pow9_17_q, f, pow9_17, pow9_17_mul_t]
  simp only [pow8_139]
  ring

theorem pow9_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_16 z * u8 z = pow9_17_q z * f z + pow9_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_17_mul_integer z


theorem pow9_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_16 z * u8 z = pow9_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_17_mul z


theorem pow9_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 17 = pow9_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow9_16_pow z hz]
  exact pow9_17_root z hz


theorem pow9_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_17 z * pow9_17 z = pow9_34_q z * f z + pow9_34 z + (139 : R) * pow9_34_mul_t z := by
  simp only [pow9_17, pow9_34_q, f, pow9_34, pow9_34_mul_t]
  
  ring

theorem pow9_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_17 z * pow9_17 z = pow9_34_q z * f z + pow9_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_34_mul_integer z


theorem pow9_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_17 z * pow9_17 z = pow9_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_34_mul z


theorem pow9_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 34 = pow9_34 z := by
  calc
    _ = u8 z ^ 17 * u8 z ^ 17 := by ring
    _ = pow9_17 z * pow9_17 z := by rw [pow9_17_pow z hz]
    _ = _ := pow9_34_root z hz


theorem pow9_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_34 z * pow9_34 z = pow9_68_q z * f z + pow9_68 z + (139 : R) * pow9_68_mul_t z := by
  simp only [pow9_34, pow9_68_q, f, pow9_68, pow9_68_mul_t]
  
  ring

theorem pow9_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_34 z * pow9_34 z = pow9_68_q z * f z + pow9_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_68_mul_integer z


theorem pow9_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_34 z * pow9_34 z = pow9_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_68_mul z


theorem pow9_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 68 = pow9_68 z := by
  calc
    _ = u8 z ^ 34 * u8 z ^ 34 := by ring
    _ = pow9_34 z * pow9_34 z := by rw [pow9_34_pow z hz]
    _ = _ := pow9_68_root z hz


theorem pow9_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_68 z * u8 z = pow9_69_q z * f z + pow9_69 z + (139 : R) * pow9_69_mul_t z := by
  simp only [pow9_68, u8, pow9_69_q, f, pow9_69, pow9_69_mul_t]
  simp only [pow8_139]
  ring

theorem pow9_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_68 z * u8 z = pow9_69_q z * f z + pow9_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_69_mul_integer z


theorem pow9_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_68 z * u8 z = pow9_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_69_mul z


theorem pow9_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 69 = pow9_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow9_68_pow z hz]
  exact pow9_69_root z hz


theorem pow9_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_69 z * pow9_69 z = pow9_138_q z * f z + pow9_138 z + (139 : R) * pow9_138_mul_t z := by
  simp only [pow9_69, pow9_138_q, f, pow9_138, pow9_138_mul_t]
  
  ring

theorem pow9_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_69 z * pow9_69 z = pow9_138_q z * f z + pow9_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_138_mul_integer z


theorem pow9_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_69 z * pow9_69 z = pow9_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_138_mul z


theorem pow9_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 138 = pow9_138 z := by
  calc
    _ = u8 z ^ 69 * u8 z ^ 69 := by ring
    _ = pow9_69 z * pow9_69 z := by rw [pow9_69_pow z hz]
    _ = _ := pow9_138_root z hz


theorem pow9_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_138 z * u8 z = pow9_139_q z * f z + pow9_139 z + (139 : R) * pow9_139_mul_t z := by
  simp only [pow9_138, u8, pow9_139_q, f, pow9_139, pow9_139_mul_t]
  simp only [pow8_139]
  ring

theorem pow9_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_138 z * u8 z = pow9_139_q z * f z + pow9_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_139_mul_integer z


theorem pow9_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_138 z * u8 z = pow9_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_139_mul z


theorem pow9_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 139 = pow9_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow9_138_pow z hz]
  exact pow9_139_root z hz


theorem iterate9 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 9) = u9 z := by
  calc
    _ = (z ^ (139 ^ 8)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u8 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate8 z hz)
    _ = _ := pow9_139_pow z hz


theorem pow10_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z + (139 : R) * pow10_2_mul_t z := by
  simp only [u9, pow10_2_q, f, pow10_2, pow10_2_mul_t]
  simp only [pow9_139]
  ring

theorem pow10_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_2_mul_integer z


theorem pow10_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z * u9 z = pow10_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_2_mul z


theorem pow10_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 2 = pow10_2 z := by
  calc
    _ = u9 z ^ 1 * u9 z ^ 1 := by ring
    _ = u9 z * u9 z := by simp only [pow_one]
    _ = _ := pow10_2_root z hz


theorem pow10_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z + (139 : R) * pow10_4_mul_t z := by
  simp only [pow10_2, pow10_4_q, f, pow10_4, pow10_4_mul_t]
  
  ring

theorem pow10_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_4_mul_integer z


theorem pow10_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_2 z * pow10_2 z = pow10_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_4_mul z


theorem pow10_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 4 = pow10_4 z := by
  calc
    _ = u9 z ^ 2 * u9 z ^ 2 := by ring
    _ = pow10_2 z * pow10_2 z := by rw [pow10_2_pow z hz]
    _ = _ := pow10_4_root z hz


theorem pow10_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_4 z * pow10_4 z = pow10_8_q z * f z + pow10_8 z + (139 : R) * pow10_8_mul_t z := by
  simp only [pow10_4, pow10_8_q, f, pow10_8, pow10_8_mul_t]
  
  ring

theorem pow10_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_4 z * pow10_4 z = pow10_8_q z * f z + pow10_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_8_mul_integer z


theorem pow10_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_4 z * pow10_4 z = pow10_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_8_mul z


theorem pow10_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 8 = pow10_8 z := by
  calc
    _ = u9 z ^ 4 * u9 z ^ 4 := by ring
    _ = pow10_4 z * pow10_4 z := by rw [pow10_4_pow z hz]
    _ = _ := pow10_8_root z hz


theorem pow10_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_8 z * pow10_8 z = pow10_16_q z * f z + pow10_16 z + (139 : R) * pow10_16_mul_t z := by
  simp only [pow10_8, pow10_16_q, f, pow10_16, pow10_16_mul_t]
  
  ring

theorem pow10_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_8 z * pow10_8 z = pow10_16_q z * f z + pow10_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_16_mul_integer z


theorem pow10_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_8 z * pow10_8 z = pow10_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_16_mul z


theorem pow10_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 16 = pow10_16 z := by
  calc
    _ = u9 z ^ 8 * u9 z ^ 8 := by ring
    _ = pow10_8 z * pow10_8 z := by rw [pow10_8_pow z hz]
    _ = _ := pow10_16_root z hz


theorem pow10_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_16 z * u9 z = pow10_17_q z * f z + pow10_17 z + (139 : R) * pow10_17_mul_t z := by
  simp only [pow10_16, u9, pow10_17_q, f, pow10_17, pow10_17_mul_t]
  simp only [pow9_139]
  ring

theorem pow10_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_16 z * u9 z = pow10_17_q z * f z + pow10_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_17_mul_integer z


theorem pow10_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_16 z * u9 z = pow10_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_17_mul z


theorem pow10_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 17 = pow10_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow10_16_pow z hz]
  exact pow10_17_root z hz


theorem pow10_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_17 z * pow10_17 z = pow10_34_q z * f z + pow10_34 z + (139 : R) * pow10_34_mul_t z := by
  simp only [pow10_17, pow10_34_q, f, pow10_34, pow10_34_mul_t]
  
  ring

theorem pow10_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_17 z * pow10_17 z = pow10_34_q z * f z + pow10_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_34_mul_integer z


theorem pow10_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_17 z * pow10_17 z = pow10_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_34_mul z


theorem pow10_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 34 = pow10_34 z := by
  calc
    _ = u9 z ^ 17 * u9 z ^ 17 := by ring
    _ = pow10_17 z * pow10_17 z := by rw [pow10_17_pow z hz]
    _ = _ := pow10_34_root z hz


theorem pow10_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_34 z * pow10_34 z = pow10_68_q z * f z + pow10_68 z + (139 : R) * pow10_68_mul_t z := by
  simp only [pow10_34, pow10_68_q, f, pow10_68, pow10_68_mul_t]
  
  ring

theorem pow10_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_34 z * pow10_34 z = pow10_68_q z * f z + pow10_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_68_mul_integer z


theorem pow10_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_34 z * pow10_34 z = pow10_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_68_mul z


theorem pow10_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 68 = pow10_68 z := by
  calc
    _ = u9 z ^ 34 * u9 z ^ 34 := by ring
    _ = pow10_34 z * pow10_34 z := by rw [pow10_34_pow z hz]
    _ = _ := pow10_68_root z hz


theorem pow10_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_68 z * u9 z = pow10_69_q z * f z + pow10_69 z + (139 : R) * pow10_69_mul_t z := by
  simp only [pow10_68, u9, pow10_69_q, f, pow10_69, pow10_69_mul_t]
  simp only [pow9_139]
  ring

theorem pow10_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_68 z * u9 z = pow10_69_q z * f z + pow10_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_69_mul_integer z


theorem pow10_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_68 z * u9 z = pow10_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_69_mul z


theorem pow10_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 69 = pow10_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow10_68_pow z hz]
  exact pow10_69_root z hz


theorem pow10_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_69 z * pow10_69 z = pow10_138_q z * f z + pow10_138 z + (139 : R) * pow10_138_mul_t z := by
  simp only [pow10_69, pow10_138_q, f, pow10_138, pow10_138_mul_t]
  
  ring

theorem pow10_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_69 z * pow10_69 z = pow10_138_q z * f z + pow10_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_138_mul_integer z


theorem pow10_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_69 z * pow10_69 z = pow10_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_138_mul z


theorem pow10_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 138 = pow10_138 z := by
  calc
    _ = u9 z ^ 69 * u9 z ^ 69 := by ring
    _ = pow10_69 z * pow10_69 z := by rw [pow10_69_pow z hz]
    _ = _ := pow10_138_root z hz


theorem pow10_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_138 z * u9 z = pow10_139_q z * f z + pow10_139 z + (139 : R) * pow10_139_mul_t z := by
  simp only [pow10_138, u9, pow10_139_q, f, pow10_139, pow10_139_mul_t]
  simp only [pow9_139]
  ring

theorem pow10_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_138 z * u9 z = pow10_139_q z * f z + pow10_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_139_mul_integer z


theorem pow10_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_138 z * u9 z = pow10_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_139_mul z


theorem pow10_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 139 = pow10_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow10_138_pow z hz]
  exact pow10_139_root z hz


theorem iterate10 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 10) = u10 z := by
  calc
    _ = (z ^ (139 ^ 9)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u9 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate9 z hz)
    _ = _ := pow10_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers06
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow11_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z + (139 : R) * pow11_2_mul_t z := by
  simp only [u10, pow11_2_q, f, pow11_2, pow11_2_mul_t]
  simp only [pow10_139]
  ring

theorem pow11_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_2_mul_integer z


theorem pow11_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z * u10 z = pow11_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_2_mul z


theorem pow11_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 2 = pow11_2 z := by
  calc
    _ = u10 z ^ 1 * u10 z ^ 1 := by ring
    _ = u10 z * u10 z := by simp only [pow_one]
    _ = _ := pow11_2_root z hz


theorem pow11_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z + (139 : R) * pow11_4_mul_t z := by
  simp only [pow11_2, pow11_4_q, f, pow11_4, pow11_4_mul_t]
  
  ring

theorem pow11_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_4_mul_integer z


theorem pow11_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_2 z * pow11_2 z = pow11_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_4_mul z


theorem pow11_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 4 = pow11_4 z := by
  calc
    _ = u10 z ^ 2 * u10 z ^ 2 := by ring
    _ = pow11_2 z * pow11_2 z := by rw [pow11_2_pow z hz]
    _ = _ := pow11_4_root z hz


theorem pow11_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_4 z * pow11_4 z = pow11_8_q z * f z + pow11_8 z + (139 : R) * pow11_8_mul_t z := by
  simp only [pow11_4, pow11_8_q, f, pow11_8, pow11_8_mul_t]
  
  ring

theorem pow11_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_4 z * pow11_4 z = pow11_8_q z * f z + pow11_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_8_mul_integer z


theorem pow11_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_4 z * pow11_4 z = pow11_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_8_mul z


theorem pow11_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 8 = pow11_8 z := by
  calc
    _ = u10 z ^ 4 * u10 z ^ 4 := by ring
    _ = pow11_4 z * pow11_4 z := by rw [pow11_4_pow z hz]
    _ = _ := pow11_8_root z hz


theorem pow11_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_8 z * pow11_8 z = pow11_16_q z * f z + pow11_16 z + (139 : R) * pow11_16_mul_t z := by
  simp only [pow11_8, pow11_16_q, f, pow11_16, pow11_16_mul_t]
  
  ring

theorem pow11_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_8 z * pow11_8 z = pow11_16_q z * f z + pow11_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_16_mul_integer z


theorem pow11_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_8 z * pow11_8 z = pow11_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_16_mul z


theorem pow11_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 16 = pow11_16 z := by
  calc
    _ = u10 z ^ 8 * u10 z ^ 8 := by ring
    _ = pow11_8 z * pow11_8 z := by rw [pow11_8_pow z hz]
    _ = _ := pow11_16_root z hz


theorem pow11_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_16 z * u10 z = pow11_17_q z * f z + pow11_17 z + (139 : R) * pow11_17_mul_t z := by
  simp only [pow11_16, u10, pow11_17_q, f, pow11_17, pow11_17_mul_t]
  simp only [pow10_139]
  ring

theorem pow11_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_16 z * u10 z = pow11_17_q z * f z + pow11_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_17_mul_integer z


theorem pow11_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_16 z * u10 z = pow11_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_17_mul z


theorem pow11_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 17 = pow11_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow11_16_pow z hz]
  exact pow11_17_root z hz


theorem pow11_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_17 z * pow11_17 z = pow11_34_q z * f z + pow11_34 z + (139 : R) * pow11_34_mul_t z := by
  simp only [pow11_17, pow11_34_q, f, pow11_34, pow11_34_mul_t]
  
  ring

theorem pow11_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_17 z * pow11_17 z = pow11_34_q z * f z + pow11_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_34_mul_integer z


theorem pow11_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_17 z * pow11_17 z = pow11_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_34_mul z


theorem pow11_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 34 = pow11_34 z := by
  calc
    _ = u10 z ^ 17 * u10 z ^ 17 := by ring
    _ = pow11_17 z * pow11_17 z := by rw [pow11_17_pow z hz]
    _ = _ := pow11_34_root z hz


theorem pow11_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_34 z * pow11_34 z = pow11_68_q z * f z + pow11_68 z + (139 : R) * pow11_68_mul_t z := by
  simp only [pow11_34, pow11_68_q, f, pow11_68, pow11_68_mul_t]
  
  ring

theorem pow11_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_34 z * pow11_34 z = pow11_68_q z * f z + pow11_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_68_mul_integer z


theorem pow11_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_34 z * pow11_34 z = pow11_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_68_mul z


theorem pow11_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 68 = pow11_68 z := by
  calc
    _ = u10 z ^ 34 * u10 z ^ 34 := by ring
    _ = pow11_34 z * pow11_34 z := by rw [pow11_34_pow z hz]
    _ = _ := pow11_68_root z hz


theorem pow11_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_68 z * u10 z = pow11_69_q z * f z + pow11_69 z + (139 : R) * pow11_69_mul_t z := by
  simp only [pow11_68, u10, pow11_69_q, f, pow11_69, pow11_69_mul_t]
  simp only [pow10_139]
  ring

theorem pow11_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_68 z * u10 z = pow11_69_q z * f z + pow11_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_69_mul_integer z


theorem pow11_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_68 z * u10 z = pow11_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_69_mul z


theorem pow11_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 69 = pow11_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow11_68_pow z hz]
  exact pow11_69_root z hz


theorem pow11_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_69 z * pow11_69 z = pow11_138_q z * f z + pow11_138 z + (139 : R) * pow11_138_mul_t z := by
  simp only [pow11_69, pow11_138_q, f, pow11_138, pow11_138_mul_t]
  
  ring

theorem pow11_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_69 z * pow11_69 z = pow11_138_q z * f z + pow11_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_138_mul_integer z


theorem pow11_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_69 z * pow11_69 z = pow11_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_138_mul z


theorem pow11_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 138 = pow11_138 z := by
  calc
    _ = u10 z ^ 69 * u10 z ^ 69 := by ring
    _ = pow11_69 z * pow11_69 z := by rw [pow11_69_pow z hz]
    _ = _ := pow11_138_root z hz


theorem pow11_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_138 z * u10 z = pow11_139_q z * f z + pow11_139 z + (139 : R) * pow11_139_mul_t z := by
  simp only [pow11_138, u10, pow11_139_q, f, pow11_139, pow11_139_mul_t]
  simp only [pow10_139]
  ring

theorem pow11_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_138 z * u10 z = pow11_139_q z * f z + pow11_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_139_mul_integer z


theorem pow11_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_138 z * u10 z = pow11_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_139_mul z


theorem pow11_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 139 = pow11_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow11_138_pow z hz]
  exact pow11_139_root z hz


theorem iterate11 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 11) = u11 z := by
  calc
    _ = (z ^ (139 ^ 10)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u10 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate10 z hz)
    _ = _ := pow11_139_pow z hz


theorem pow12_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z + (139 : R) * pow12_2_mul_t z := by
  simp only [u11, pow12_2_q, f, pow12_2, pow12_2_mul_t]
  simp only [pow11_139]
  ring

theorem pow12_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_2_mul_integer z


theorem pow12_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z * u11 z = pow12_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_2_mul z


theorem pow12_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 2 = pow12_2 z := by
  calc
    _ = u11 z ^ 1 * u11 z ^ 1 := by ring
    _ = u11 z * u11 z := by simp only [pow_one]
    _ = _ := pow12_2_root z hz


theorem pow12_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z + (139 : R) * pow12_4_mul_t z := by
  simp only [pow12_2, pow12_4_q, f, pow12_4, pow12_4_mul_t]
  
  ring

theorem pow12_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_4_mul_integer z


theorem pow12_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_2 z * pow12_2 z = pow12_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_4_mul z


theorem pow12_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 4 = pow12_4 z := by
  calc
    _ = u11 z ^ 2 * u11 z ^ 2 := by ring
    _ = pow12_2 z * pow12_2 z := by rw [pow12_2_pow z hz]
    _ = _ := pow12_4_root z hz


theorem pow12_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_4 z * pow12_4 z = pow12_8_q z * f z + pow12_8 z + (139 : R) * pow12_8_mul_t z := by
  simp only [pow12_4, pow12_8_q, f, pow12_8, pow12_8_mul_t]
  
  ring

theorem pow12_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_4 z * pow12_4 z = pow12_8_q z * f z + pow12_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_8_mul_integer z


theorem pow12_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_4 z * pow12_4 z = pow12_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_8_mul z


theorem pow12_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 8 = pow12_8 z := by
  calc
    _ = u11 z ^ 4 * u11 z ^ 4 := by ring
    _ = pow12_4 z * pow12_4 z := by rw [pow12_4_pow z hz]
    _ = _ := pow12_8_root z hz


theorem pow12_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_8 z * pow12_8 z = pow12_16_q z * f z + pow12_16 z + (139 : R) * pow12_16_mul_t z := by
  simp only [pow12_8, pow12_16_q, f, pow12_16, pow12_16_mul_t]
  
  ring

theorem pow12_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_8 z * pow12_8 z = pow12_16_q z * f z + pow12_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_16_mul_integer z


theorem pow12_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_8 z * pow12_8 z = pow12_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_16_mul z


theorem pow12_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 16 = pow12_16 z := by
  calc
    _ = u11 z ^ 8 * u11 z ^ 8 := by ring
    _ = pow12_8 z * pow12_8 z := by rw [pow12_8_pow z hz]
    _ = _ := pow12_16_root z hz


theorem pow12_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_16 z * u11 z = pow12_17_q z * f z + pow12_17 z + (139 : R) * pow12_17_mul_t z := by
  simp only [pow12_16, u11, pow12_17_q, f, pow12_17, pow12_17_mul_t]
  simp only [pow11_139]
  ring

theorem pow12_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_16 z * u11 z = pow12_17_q z * f z + pow12_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_17_mul_integer z


theorem pow12_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_16 z * u11 z = pow12_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_17_mul z


theorem pow12_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 17 = pow12_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow12_16_pow z hz]
  exact pow12_17_root z hz


theorem pow12_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_17 z * pow12_17 z = pow12_34_q z * f z + pow12_34 z + (139 : R) * pow12_34_mul_t z := by
  simp only [pow12_17, pow12_34_q, f, pow12_34, pow12_34_mul_t]
  
  ring

theorem pow12_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_17 z * pow12_17 z = pow12_34_q z * f z + pow12_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_34_mul_integer z


theorem pow12_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_17 z * pow12_17 z = pow12_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_34_mul z


theorem pow12_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 34 = pow12_34 z := by
  calc
    _ = u11 z ^ 17 * u11 z ^ 17 := by ring
    _ = pow12_17 z * pow12_17 z := by rw [pow12_17_pow z hz]
    _ = _ := pow12_34_root z hz


theorem pow12_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_34 z * pow12_34 z = pow12_68_q z * f z + pow12_68 z + (139 : R) * pow12_68_mul_t z := by
  simp only [pow12_34, pow12_68_q, f, pow12_68, pow12_68_mul_t]
  
  ring

theorem pow12_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_34 z * pow12_34 z = pow12_68_q z * f z + pow12_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_68_mul_integer z


theorem pow12_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_34 z * pow12_34 z = pow12_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_68_mul z


theorem pow12_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 68 = pow12_68 z := by
  calc
    _ = u11 z ^ 34 * u11 z ^ 34 := by ring
    _ = pow12_34 z * pow12_34 z := by rw [pow12_34_pow z hz]
    _ = _ := pow12_68_root z hz


theorem pow12_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_68 z * u11 z = pow12_69_q z * f z + pow12_69 z + (139 : R) * pow12_69_mul_t z := by
  simp only [pow12_68, u11, pow12_69_q, f, pow12_69, pow12_69_mul_t]
  simp only [pow11_139]
  ring

theorem pow12_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_68 z * u11 z = pow12_69_q z * f z + pow12_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_69_mul_integer z


theorem pow12_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_68 z * u11 z = pow12_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_69_mul z


theorem pow12_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 69 = pow12_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow12_68_pow z hz]
  exact pow12_69_root z hz


theorem pow12_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_69 z * pow12_69 z = pow12_138_q z * f z + pow12_138 z + (139 : R) * pow12_138_mul_t z := by
  simp only [pow12_69, pow12_138_q, f, pow12_138, pow12_138_mul_t]
  
  ring

theorem pow12_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_69 z * pow12_69 z = pow12_138_q z * f z + pow12_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_138_mul_integer z


theorem pow12_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_69 z * pow12_69 z = pow12_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_138_mul z


theorem pow12_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 138 = pow12_138 z := by
  calc
    _ = u11 z ^ 69 * u11 z ^ 69 := by ring
    _ = pow12_69 z * pow12_69 z := by rw [pow12_69_pow z hz]
    _ = _ := pow12_138_root z hz


theorem pow12_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_138 z * u11 z = pow12_139_q z * f z + pow12_139 z + (139 : R) * pow12_139_mul_t z := by
  simp only [pow12_138, u11, pow12_139_q, f, pow12_139, pow12_139_mul_t]
  simp only [pow11_139]
  ring

theorem pow12_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_138 z * u11 z = pow12_139_q z * f z + pow12_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_139_mul_integer z


theorem pow12_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_138 z * u11 z = pow12_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_139_mul z


theorem pow12_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 139 = pow12_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow12_138_pow z hz]
  exact pow12_139_root z hz


theorem iterate12_oai {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 12) = u12 z := by
  calc
    _ = (z ^ (139 ^ 11)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u11 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate11 z hz)
    _ = _ := pow12_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Mod139.iterate12_oai.{u_1} := @OAI.DimensionTen.Mod139.iterate12_oai.{u_1}
