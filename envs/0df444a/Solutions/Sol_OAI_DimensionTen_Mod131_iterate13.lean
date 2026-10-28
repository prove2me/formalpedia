-- Prove2me | solution 1 for OAI.DimensionTen.Mod131.iterate13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:13:27.19761+00:00
-- url     : https://prove2.me/submissions/8b8ff33b-d4dd-4d73-aa98-30115ac712c2

import Mathlib
import Definitions.Def_OAIQ033D013
import Theorems.Thm_OAI_DimensionTen_Mod131_iterate7

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers04
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow8_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z + (131 : R) * pow8_2_mul_t z := by
  simp only [u7, pow8_2_q, f, pow8_2, pow8_2_mul_t]
  simp only [pow7_131]
  ring

theorem pow8_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_2_mul_integer z


theorem pow8_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z * u7 z = pow8_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_2_mul z


theorem pow8_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 2 = pow8_2 z := by
  calc
    _ = u7 z ^ 1 * u7 z ^ 1 := by ring
    _ = u7 z * u7 z := by simp only [pow_one]
    _ = _ := pow8_2_root z hz


theorem pow8_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z + (131 : R) * pow8_4_mul_t z := by
  simp only [pow8_2, pow8_4_q, f, pow8_4, pow8_4_mul_t]
  
  ring

theorem pow8_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_4_mul_integer z


theorem pow8_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_2 z * pow8_2 z = pow8_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_4_mul z


theorem pow8_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 4 = pow8_4 z := by
  calc
    _ = u7 z ^ 2 * u7 z ^ 2 := by ring
    _ = pow8_2 z * pow8_2 z := by rw [pow8_2_pow z hz]
    _ = _ := pow8_4_root z hz


theorem pow8_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_4 z * pow8_4 z = pow8_8_q z * f z + pow8_8 z + (131 : R) * pow8_8_mul_t z := by
  simp only [pow8_4, pow8_8_q, f, pow8_8, pow8_8_mul_t]
  
  ring

theorem pow8_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_4 z * pow8_4 z = pow8_8_q z * f z + pow8_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_8_mul_integer z


theorem pow8_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_4 z * pow8_4 z = pow8_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_8_mul z


theorem pow8_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 8 = pow8_8 z := by
  calc
    _ = u7 z ^ 4 * u7 z ^ 4 := by ring
    _ = pow8_4 z * pow8_4 z := by rw [pow8_4_pow z hz]
    _ = _ := pow8_8_root z hz


theorem pow8_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_8 z * pow8_8 z = pow8_16_q z * f z + pow8_16 z + (131 : R) * pow8_16_mul_t z := by
  simp only [pow8_8, pow8_16_q, f, pow8_16, pow8_16_mul_t]
  
  ring

theorem pow8_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_8 z * pow8_8 z = pow8_16_q z * f z + pow8_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_16_mul_integer z


theorem pow8_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_8 z * pow8_8 z = pow8_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_16_mul z


theorem pow8_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 16 = pow8_16 z := by
  calc
    _ = u7 z ^ 8 * u7 z ^ 8 := by ring
    _ = pow8_8 z * pow8_8 z := by rw [pow8_8_pow z hz]
    _ = _ := pow8_16_root z hz


theorem pow8_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_16 z * pow8_16 z = pow8_32_q z * f z + pow8_32 z + (131 : R) * pow8_32_mul_t z := by
  simp only [pow8_16, pow8_32_q, f, pow8_32, pow8_32_mul_t]
  
  ring

theorem pow8_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_16 z * pow8_16 z = pow8_32_q z * f z + pow8_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_32_mul_integer z


theorem pow8_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_16 z * pow8_16 z = pow8_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_32_mul z


theorem pow8_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 32 = pow8_32 z := by
  calc
    _ = u7 z ^ 16 * u7 z ^ 16 := by ring
    _ = pow8_16 z * pow8_16 z := by rw [pow8_16_pow z hz]
    _ = _ := pow8_32_root z hz


theorem pow8_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_32 z * pow8_32 z = pow8_64_q z * f z + pow8_64 z + (131 : R) * pow8_64_mul_t z := by
  simp only [pow8_32, pow8_64_q, f, pow8_64, pow8_64_mul_t]
  
  ring

theorem pow8_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_32 z * pow8_32 z = pow8_64_q z * f z + pow8_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_64_mul_integer z


theorem pow8_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_32 z * pow8_32 z = pow8_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_64_mul z


theorem pow8_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 64 = pow8_64 z := by
  calc
    _ = u7 z ^ 32 * u7 z ^ 32 := by ring
    _ = pow8_32 z * pow8_32 z := by rw [pow8_32_pow z hz]
    _ = _ := pow8_64_root z hz


theorem pow8_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_64 z * u7 z = pow8_65_q z * f z + pow8_65 z + (131 : R) * pow8_65_mul_t z := by
  simp only [pow8_64, u7, pow8_65_q, f, pow8_65, pow8_65_mul_t]
  simp only [pow7_131]
  ring

theorem pow8_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_64 z * u7 z = pow8_65_q z * f z + pow8_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_65_mul_integer z


theorem pow8_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_64 z * u7 z = pow8_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_65_mul z


theorem pow8_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 65 = pow8_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow8_64_pow z hz]
  exact pow8_65_root z hz


theorem pow8_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_65 z * pow8_65 z = pow8_130_q z * f z + pow8_130 z + (131 : R) * pow8_130_mul_t z := by
  simp only [pow8_65, pow8_130_q, f, pow8_130, pow8_130_mul_t]
  
  ring

theorem pow8_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_65 z * pow8_65 z = pow8_130_q z * f z + pow8_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_130_mul_integer z


theorem pow8_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_65 z * pow8_65 z = pow8_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_130_mul z


theorem pow8_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 130 = pow8_130 z := by
  calc
    _ = u7 z ^ 65 * u7 z ^ 65 := by ring
    _ = pow8_65 z * pow8_65 z := by rw [pow8_65_pow z hz]
    _ = _ := pow8_130_root z hz


theorem pow8_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_130 z * u7 z = pow8_131_q z * f z + pow8_131 z + (131 : R) * pow8_131_mul_t z := by
  simp only [pow8_130, u7, pow8_131_q, f, pow8_131, pow8_131_mul_t]
  simp only [pow7_131]
  ring

theorem pow8_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_130 z * u7 z = pow8_131_q z * f z + pow8_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_131_mul_integer z


theorem pow8_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_130 z * u7 z = pow8_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_131_mul z


theorem pow8_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 131 = pow8_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow8_130_pow z hz]
  exact pow8_131_root z hz


theorem iterate8 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 8) = u8 z := by
  calc
    _ = (z ^ (131 ^ 7)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u7 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate7 z hz)
    _ = _ := pow8_131_pow z hz

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers05
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow9_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z + (131 : R) * pow9_2_mul_t z := by
  simp only [u8, pow9_2_q, f, pow9_2, pow9_2_mul_t]
  simp only [pow8_131]
  ring

theorem pow9_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_2_mul_integer z


theorem pow9_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z * u8 z = pow9_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_2_mul z


theorem pow9_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 2 = pow9_2 z := by
  calc
    _ = u8 z ^ 1 * u8 z ^ 1 := by ring
    _ = u8 z * u8 z := by simp only [pow_one]
    _ = _ := pow9_2_root z hz


theorem pow9_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z + (131 : R) * pow9_4_mul_t z := by
  simp only [pow9_2, pow9_4_q, f, pow9_4, pow9_4_mul_t]
  
  ring

theorem pow9_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_4_mul_integer z


theorem pow9_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_2 z * pow9_2 z = pow9_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_4_mul z


theorem pow9_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 4 = pow9_4 z := by
  calc
    _ = u8 z ^ 2 * u8 z ^ 2 := by ring
    _ = pow9_2 z * pow9_2 z := by rw [pow9_2_pow z hz]
    _ = _ := pow9_4_root z hz


theorem pow9_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_4 z * pow9_4 z = pow9_8_q z * f z + pow9_8 z + (131 : R) * pow9_8_mul_t z := by
  simp only [pow9_4, pow9_8_q, f, pow9_8, pow9_8_mul_t]
  
  ring

theorem pow9_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_4 z * pow9_4 z = pow9_8_q z * f z + pow9_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_8_mul_integer z


theorem pow9_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_4 z * pow9_4 z = pow9_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_8_mul z


theorem pow9_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 8 = pow9_8 z := by
  calc
    _ = u8 z ^ 4 * u8 z ^ 4 := by ring
    _ = pow9_4 z * pow9_4 z := by rw [pow9_4_pow z hz]
    _ = _ := pow9_8_root z hz


theorem pow9_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_8 z * pow9_8 z = pow9_16_q z * f z + pow9_16 z + (131 : R) * pow9_16_mul_t z := by
  simp only [pow9_8, pow9_16_q, f, pow9_16, pow9_16_mul_t]
  
  ring

theorem pow9_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_8 z * pow9_8 z = pow9_16_q z * f z + pow9_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_16_mul_integer z


theorem pow9_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_8 z * pow9_8 z = pow9_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_16_mul z


theorem pow9_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 16 = pow9_16 z := by
  calc
    _ = u8 z ^ 8 * u8 z ^ 8 := by ring
    _ = pow9_8 z * pow9_8 z := by rw [pow9_8_pow z hz]
    _ = _ := pow9_16_root z hz


theorem pow9_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_16 z * pow9_16 z = pow9_32_q z * f z + pow9_32 z + (131 : R) * pow9_32_mul_t z := by
  simp only [pow9_16, pow9_32_q, f, pow9_32, pow9_32_mul_t]
  
  ring

theorem pow9_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_16 z * pow9_16 z = pow9_32_q z * f z + pow9_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_32_mul_integer z


theorem pow9_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_16 z * pow9_16 z = pow9_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_32_mul z


theorem pow9_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 32 = pow9_32 z := by
  calc
    _ = u8 z ^ 16 * u8 z ^ 16 := by ring
    _ = pow9_16 z * pow9_16 z := by rw [pow9_16_pow z hz]
    _ = _ := pow9_32_root z hz


theorem pow9_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_32 z * pow9_32 z = pow9_64_q z * f z + pow9_64 z + (131 : R) * pow9_64_mul_t z := by
  simp only [pow9_32, pow9_64_q, f, pow9_64, pow9_64_mul_t]
  
  ring

theorem pow9_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_32 z * pow9_32 z = pow9_64_q z * f z + pow9_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_64_mul_integer z


theorem pow9_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_32 z * pow9_32 z = pow9_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_64_mul z


theorem pow9_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 64 = pow9_64 z := by
  calc
    _ = u8 z ^ 32 * u8 z ^ 32 := by ring
    _ = pow9_32 z * pow9_32 z := by rw [pow9_32_pow z hz]
    _ = _ := pow9_64_root z hz


theorem pow9_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_64 z * u8 z = pow9_65_q z * f z + pow9_65 z + (131 : R) * pow9_65_mul_t z := by
  simp only [pow9_64, u8, pow9_65_q, f, pow9_65, pow9_65_mul_t]
  simp only [pow8_131]
  ring

theorem pow9_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_64 z * u8 z = pow9_65_q z * f z + pow9_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_65_mul_integer z


theorem pow9_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_64 z * u8 z = pow9_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_65_mul z


theorem pow9_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 65 = pow9_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow9_64_pow z hz]
  exact pow9_65_root z hz


theorem pow9_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_65 z * pow9_65 z = pow9_130_q z * f z + pow9_130 z + (131 : R) * pow9_130_mul_t z := by
  simp only [pow9_65, pow9_130_q, f, pow9_130, pow9_130_mul_t]
  
  ring

theorem pow9_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_65 z * pow9_65 z = pow9_130_q z * f z + pow9_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_130_mul_integer z


theorem pow9_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_65 z * pow9_65 z = pow9_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_130_mul z


theorem pow9_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 130 = pow9_130 z := by
  calc
    _ = u8 z ^ 65 * u8 z ^ 65 := by ring
    _ = pow9_65 z * pow9_65 z := by rw [pow9_65_pow z hz]
    _ = _ := pow9_130_root z hz


theorem pow9_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_130 z * u8 z = pow9_131_q z * f z + pow9_131 z + (131 : R) * pow9_131_mul_t z := by
  simp only [pow9_130, u8, pow9_131_q, f, pow9_131, pow9_131_mul_t]
  simp only [pow8_131]
  ring

theorem pow9_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_130 z * u8 z = pow9_131_q z * f z + pow9_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_131_mul_integer z


theorem pow9_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_130 z * u8 z = pow9_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_131_mul z


theorem pow9_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 131 = pow9_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow9_130_pow z hz]
  exact pow9_131_root z hz


theorem iterate9 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 9) = u9 z := by
  calc
    _ = (z ^ (131 ^ 8)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u8 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate8 z hz)
    _ = _ := pow9_131_pow z hz


theorem pow10_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z + (131 : R) * pow10_2_mul_t z := by
  simp only [u9, pow10_2_q, f, pow10_2, pow10_2_mul_t]
  simp only [pow9_131]
  ring

theorem pow10_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_2_mul_integer z


theorem pow10_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z * u9 z = pow10_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_2_mul z


theorem pow10_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 2 = pow10_2 z := by
  calc
    _ = u9 z ^ 1 * u9 z ^ 1 := by ring
    _ = u9 z * u9 z := by simp only [pow_one]
    _ = _ := pow10_2_root z hz


theorem pow10_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z + (131 : R) * pow10_4_mul_t z := by
  simp only [pow10_2, pow10_4_q, f, pow10_4, pow10_4_mul_t]
  
  ring

theorem pow10_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_4_mul_integer z


theorem pow10_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_2 z * pow10_2 z = pow10_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_4_mul z


theorem pow10_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 4 = pow10_4 z := by
  calc
    _ = u9 z ^ 2 * u9 z ^ 2 := by ring
    _ = pow10_2 z * pow10_2 z := by rw [pow10_2_pow z hz]
    _ = _ := pow10_4_root z hz


theorem pow10_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_4 z * pow10_4 z = pow10_8_q z * f z + pow10_8 z + (131 : R) * pow10_8_mul_t z := by
  simp only [pow10_4, pow10_8_q, f, pow10_8, pow10_8_mul_t]
  
  ring

theorem pow10_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_4 z * pow10_4 z = pow10_8_q z * f z + pow10_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_8_mul_integer z


theorem pow10_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_4 z * pow10_4 z = pow10_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_8_mul z


theorem pow10_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 8 = pow10_8 z := by
  calc
    _ = u9 z ^ 4 * u9 z ^ 4 := by ring
    _ = pow10_4 z * pow10_4 z := by rw [pow10_4_pow z hz]
    _ = _ := pow10_8_root z hz


theorem pow10_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_8 z * pow10_8 z = pow10_16_q z * f z + pow10_16 z + (131 : R) * pow10_16_mul_t z := by
  simp only [pow10_8, pow10_16_q, f, pow10_16, pow10_16_mul_t]
  
  ring

theorem pow10_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_8 z * pow10_8 z = pow10_16_q z * f z + pow10_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_16_mul_integer z


theorem pow10_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_8 z * pow10_8 z = pow10_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_16_mul z


theorem pow10_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 16 = pow10_16 z := by
  calc
    _ = u9 z ^ 8 * u9 z ^ 8 := by ring
    _ = pow10_8 z * pow10_8 z := by rw [pow10_8_pow z hz]
    _ = _ := pow10_16_root z hz


theorem pow10_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_16 z * pow10_16 z = pow10_32_q z * f z + pow10_32 z + (131 : R) * pow10_32_mul_t z := by
  simp only [pow10_16, pow10_32_q, f, pow10_32, pow10_32_mul_t]
  
  ring

theorem pow10_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_16 z * pow10_16 z = pow10_32_q z * f z + pow10_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_32_mul_integer z


theorem pow10_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_16 z * pow10_16 z = pow10_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_32_mul z


theorem pow10_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 32 = pow10_32 z := by
  calc
    _ = u9 z ^ 16 * u9 z ^ 16 := by ring
    _ = pow10_16 z * pow10_16 z := by rw [pow10_16_pow z hz]
    _ = _ := pow10_32_root z hz


theorem pow10_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_32 z * pow10_32 z = pow10_64_q z * f z + pow10_64 z + (131 : R) * pow10_64_mul_t z := by
  simp only [pow10_32, pow10_64_q, f, pow10_64, pow10_64_mul_t]
  
  ring

theorem pow10_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_32 z * pow10_32 z = pow10_64_q z * f z + pow10_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_64_mul_integer z


theorem pow10_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_32 z * pow10_32 z = pow10_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_64_mul z


theorem pow10_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 64 = pow10_64 z := by
  calc
    _ = u9 z ^ 32 * u9 z ^ 32 := by ring
    _ = pow10_32 z * pow10_32 z := by rw [pow10_32_pow z hz]
    _ = _ := pow10_64_root z hz


theorem pow10_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_64 z * u9 z = pow10_65_q z * f z + pow10_65 z + (131 : R) * pow10_65_mul_t z := by
  simp only [pow10_64, u9, pow10_65_q, f, pow10_65, pow10_65_mul_t]
  simp only [pow9_131]
  ring

theorem pow10_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_64 z * u9 z = pow10_65_q z * f z + pow10_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_65_mul_integer z


theorem pow10_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_64 z * u9 z = pow10_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_65_mul z


theorem pow10_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 65 = pow10_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow10_64_pow z hz]
  exact pow10_65_root z hz


theorem pow10_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_65 z * pow10_65 z = pow10_130_q z * f z + pow10_130 z + (131 : R) * pow10_130_mul_t z := by
  simp only [pow10_65, pow10_130_q, f, pow10_130, pow10_130_mul_t]
  
  ring

theorem pow10_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_65 z * pow10_65 z = pow10_130_q z * f z + pow10_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_130_mul_integer z


theorem pow10_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_65 z * pow10_65 z = pow10_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_130_mul z


theorem pow10_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 130 = pow10_130 z := by
  calc
    _ = u9 z ^ 65 * u9 z ^ 65 := by ring
    _ = pow10_65 z * pow10_65 z := by rw [pow10_65_pow z hz]
    _ = _ := pow10_130_root z hz


theorem pow10_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_130 z * u9 z = pow10_131_q z * f z + pow10_131 z + (131 : R) * pow10_131_mul_t z := by
  simp only [pow10_130, u9, pow10_131_q, f, pow10_131, pow10_131_mul_t]
  simp only [pow9_131]
  ring

theorem pow10_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_130 z * u9 z = pow10_131_q z * f z + pow10_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_131_mul_integer z


theorem pow10_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_130 z * u9 z = pow10_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_131_mul z


theorem pow10_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 131 = pow10_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow10_130_pow z hz]
  exact pow10_131_root z hz


theorem iterate10 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 10) = u10 z := by
  calc
    _ = (z ^ (131 ^ 9)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u9 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate9 z hz)
    _ = _ := pow10_131_pow z hz

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers06
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow11_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z + (131 : R) * pow11_2_mul_t z := by
  simp only [u10, pow11_2_q, f, pow11_2, pow11_2_mul_t]
  simp only [pow10_131]
  ring

theorem pow11_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_2_mul_integer z


theorem pow11_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z * u10 z = pow11_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_2_mul z


theorem pow11_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 2 = pow11_2 z := by
  calc
    _ = u10 z ^ 1 * u10 z ^ 1 := by ring
    _ = u10 z * u10 z := by simp only [pow_one]
    _ = _ := pow11_2_root z hz


theorem pow11_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z + (131 : R) * pow11_4_mul_t z := by
  simp only [pow11_2, pow11_4_q, f, pow11_4, pow11_4_mul_t]
  
  ring

theorem pow11_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_4_mul_integer z


theorem pow11_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_2 z * pow11_2 z = pow11_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_4_mul z


theorem pow11_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 4 = pow11_4 z := by
  calc
    _ = u10 z ^ 2 * u10 z ^ 2 := by ring
    _ = pow11_2 z * pow11_2 z := by rw [pow11_2_pow z hz]
    _ = _ := pow11_4_root z hz


theorem pow11_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_4 z * pow11_4 z = pow11_8_q z * f z + pow11_8 z + (131 : R) * pow11_8_mul_t z := by
  simp only [pow11_4, pow11_8_q, f, pow11_8, pow11_8_mul_t]
  
  ring

theorem pow11_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_4 z * pow11_4 z = pow11_8_q z * f z + pow11_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_8_mul_integer z


theorem pow11_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_4 z * pow11_4 z = pow11_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_8_mul z


theorem pow11_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 8 = pow11_8 z := by
  calc
    _ = u10 z ^ 4 * u10 z ^ 4 := by ring
    _ = pow11_4 z * pow11_4 z := by rw [pow11_4_pow z hz]
    _ = _ := pow11_8_root z hz


theorem pow11_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_8 z * pow11_8 z = pow11_16_q z * f z + pow11_16 z + (131 : R) * pow11_16_mul_t z := by
  simp only [pow11_8, pow11_16_q, f, pow11_16, pow11_16_mul_t]
  
  ring

theorem pow11_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_8 z * pow11_8 z = pow11_16_q z * f z + pow11_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_16_mul_integer z


theorem pow11_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_8 z * pow11_8 z = pow11_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_16_mul z


theorem pow11_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 16 = pow11_16 z := by
  calc
    _ = u10 z ^ 8 * u10 z ^ 8 := by ring
    _ = pow11_8 z * pow11_8 z := by rw [pow11_8_pow z hz]
    _ = _ := pow11_16_root z hz


theorem pow11_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_16 z * pow11_16 z = pow11_32_q z * f z + pow11_32 z + (131 : R) * pow11_32_mul_t z := by
  simp only [pow11_16, pow11_32_q, f, pow11_32, pow11_32_mul_t]
  
  ring

theorem pow11_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_16 z * pow11_16 z = pow11_32_q z * f z + pow11_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_32_mul_integer z


theorem pow11_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_16 z * pow11_16 z = pow11_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_32_mul z


theorem pow11_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 32 = pow11_32 z := by
  calc
    _ = u10 z ^ 16 * u10 z ^ 16 := by ring
    _ = pow11_16 z * pow11_16 z := by rw [pow11_16_pow z hz]
    _ = _ := pow11_32_root z hz


theorem pow11_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_32 z * pow11_32 z = pow11_64_q z * f z + pow11_64 z + (131 : R) * pow11_64_mul_t z := by
  simp only [pow11_32, pow11_64_q, f, pow11_64, pow11_64_mul_t]
  
  ring

theorem pow11_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_32 z * pow11_32 z = pow11_64_q z * f z + pow11_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_64_mul_integer z


theorem pow11_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_32 z * pow11_32 z = pow11_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_64_mul z


theorem pow11_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 64 = pow11_64 z := by
  calc
    _ = u10 z ^ 32 * u10 z ^ 32 := by ring
    _ = pow11_32 z * pow11_32 z := by rw [pow11_32_pow z hz]
    _ = _ := pow11_64_root z hz


theorem pow11_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_64 z * u10 z = pow11_65_q z * f z + pow11_65 z + (131 : R) * pow11_65_mul_t z := by
  simp only [pow11_64, u10, pow11_65_q, f, pow11_65, pow11_65_mul_t]
  simp only [pow10_131]
  ring

theorem pow11_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_64 z * u10 z = pow11_65_q z * f z + pow11_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_65_mul_integer z


theorem pow11_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_64 z * u10 z = pow11_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_65_mul z


theorem pow11_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 65 = pow11_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow11_64_pow z hz]
  exact pow11_65_root z hz


theorem pow11_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_65 z * pow11_65 z = pow11_130_q z * f z + pow11_130 z + (131 : R) * pow11_130_mul_t z := by
  simp only [pow11_65, pow11_130_q, f, pow11_130, pow11_130_mul_t]
  
  ring

theorem pow11_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_65 z * pow11_65 z = pow11_130_q z * f z + pow11_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_130_mul_integer z


theorem pow11_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_65 z * pow11_65 z = pow11_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_130_mul z


theorem pow11_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 130 = pow11_130 z := by
  calc
    _ = u10 z ^ 65 * u10 z ^ 65 := by ring
    _ = pow11_65 z * pow11_65 z := by rw [pow11_65_pow z hz]
    _ = _ := pow11_130_root z hz


theorem pow11_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_130 z * u10 z = pow11_131_q z * f z + pow11_131 z + (131 : R) * pow11_131_mul_t z := by
  simp only [pow11_130, u10, pow11_131_q, f, pow11_131, pow11_131_mul_t]
  simp only [pow10_131]
  ring

theorem pow11_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_130 z * u10 z = pow11_131_q z * f z + pow11_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_131_mul_integer z


theorem pow11_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_130 z * u10 z = pow11_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_131_mul z


theorem pow11_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 131 = pow11_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow11_130_pow z hz]
  exact pow11_131_root z hz


theorem iterate11 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 11) = u11 z := by
  calc
    _ = (z ^ (131 ^ 10)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u10 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate10 z hz)
    _ = _ := pow11_131_pow z hz


theorem pow12_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z + (131 : R) * pow12_2_mul_t z := by
  simp only [u11, pow12_2_q, f, pow12_2, pow12_2_mul_t]
  simp only [pow11_131]
  ring

theorem pow12_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_2_mul_integer z


theorem pow12_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z * u11 z = pow12_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_2_mul z


theorem pow12_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 2 = pow12_2 z := by
  calc
    _ = u11 z ^ 1 * u11 z ^ 1 := by ring
    _ = u11 z * u11 z := by simp only [pow_one]
    _ = _ := pow12_2_root z hz


theorem pow12_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z + (131 : R) * pow12_4_mul_t z := by
  simp only [pow12_2, pow12_4_q, f, pow12_4, pow12_4_mul_t]
  
  ring

theorem pow12_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_4_mul_integer z


theorem pow12_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_2 z * pow12_2 z = pow12_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_4_mul z


theorem pow12_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 4 = pow12_4 z := by
  calc
    _ = u11 z ^ 2 * u11 z ^ 2 := by ring
    _ = pow12_2 z * pow12_2 z := by rw [pow12_2_pow z hz]
    _ = _ := pow12_4_root z hz


theorem pow12_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_4 z * pow12_4 z = pow12_8_q z * f z + pow12_8 z + (131 : R) * pow12_8_mul_t z := by
  simp only [pow12_4, pow12_8_q, f, pow12_8, pow12_8_mul_t]
  
  ring

theorem pow12_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_4 z * pow12_4 z = pow12_8_q z * f z + pow12_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_8_mul_integer z


theorem pow12_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_4 z * pow12_4 z = pow12_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_8_mul z


theorem pow12_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 8 = pow12_8 z := by
  calc
    _ = u11 z ^ 4 * u11 z ^ 4 := by ring
    _ = pow12_4 z * pow12_4 z := by rw [pow12_4_pow z hz]
    _ = _ := pow12_8_root z hz


theorem pow12_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_8 z * pow12_8 z = pow12_16_q z * f z + pow12_16 z + (131 : R) * pow12_16_mul_t z := by
  simp only [pow12_8, pow12_16_q, f, pow12_16, pow12_16_mul_t]
  
  ring

theorem pow12_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_8 z * pow12_8 z = pow12_16_q z * f z + pow12_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_16_mul_integer z


theorem pow12_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_8 z * pow12_8 z = pow12_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_16_mul z


theorem pow12_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 16 = pow12_16 z := by
  calc
    _ = u11 z ^ 8 * u11 z ^ 8 := by ring
    _ = pow12_8 z * pow12_8 z := by rw [pow12_8_pow z hz]
    _ = _ := pow12_16_root z hz


theorem pow12_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_16 z * pow12_16 z = pow12_32_q z * f z + pow12_32 z + (131 : R) * pow12_32_mul_t z := by
  simp only [pow12_16, pow12_32_q, f, pow12_32, pow12_32_mul_t]
  
  ring

theorem pow12_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_16 z * pow12_16 z = pow12_32_q z * f z + pow12_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_32_mul_integer z


theorem pow12_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_16 z * pow12_16 z = pow12_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_32_mul z


theorem pow12_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 32 = pow12_32 z := by
  calc
    _ = u11 z ^ 16 * u11 z ^ 16 := by ring
    _ = pow12_16 z * pow12_16 z := by rw [pow12_16_pow z hz]
    _ = _ := pow12_32_root z hz


theorem pow12_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_32 z * pow12_32 z = pow12_64_q z * f z + pow12_64 z + (131 : R) * pow12_64_mul_t z := by
  simp only [pow12_32, pow12_64_q, f, pow12_64, pow12_64_mul_t]
  
  ring

theorem pow12_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_32 z * pow12_32 z = pow12_64_q z * f z + pow12_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_64_mul_integer z


theorem pow12_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_32 z * pow12_32 z = pow12_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_64_mul z


theorem pow12_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 64 = pow12_64 z := by
  calc
    _ = u11 z ^ 32 * u11 z ^ 32 := by ring
    _ = pow12_32 z * pow12_32 z := by rw [pow12_32_pow z hz]
    _ = _ := pow12_64_root z hz


theorem pow12_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_64 z * u11 z = pow12_65_q z * f z + pow12_65 z + (131 : R) * pow12_65_mul_t z := by
  simp only [pow12_64, u11, pow12_65_q, f, pow12_65, pow12_65_mul_t]
  simp only [pow11_131]
  ring

theorem pow12_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_64 z * u11 z = pow12_65_q z * f z + pow12_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_65_mul_integer z


theorem pow12_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_64 z * u11 z = pow12_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_65_mul z


theorem pow12_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 65 = pow12_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow12_64_pow z hz]
  exact pow12_65_root z hz


theorem pow12_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_65 z * pow12_65 z = pow12_130_q z * f z + pow12_130 z + (131 : R) * pow12_130_mul_t z := by
  simp only [pow12_65, pow12_130_q, f, pow12_130, pow12_130_mul_t]
  
  ring

theorem pow12_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_65 z * pow12_65 z = pow12_130_q z * f z + pow12_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_130_mul_integer z


theorem pow12_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_65 z * pow12_65 z = pow12_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_130_mul z


theorem pow12_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 130 = pow12_130 z := by
  calc
    _ = u11 z ^ 65 * u11 z ^ 65 := by ring
    _ = pow12_65 z * pow12_65 z := by rw [pow12_65_pow z hz]
    _ = _ := pow12_130_root z hz


theorem pow12_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_130 z * u11 z = pow12_131_q z * f z + pow12_131 z + (131 : R) * pow12_131_mul_t z := by
  simp only [pow12_130, u11, pow12_131_q, f, pow12_131, pow12_131_mul_t]
  simp only [pow11_131]
  ring

theorem pow12_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_130 z * u11 z = pow12_131_q z * f z + pow12_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_131_mul_integer z


theorem pow12_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_130 z * u11 z = pow12_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_131_mul z


theorem pow12_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 131 = pow12_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow12_130_pow z hz]
  exact pow12_131_root z hz


theorem iterate12 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 12) = u12 z := by
  calc
    _ = (z ^ (131 ^ 11)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u11 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate11 z hz)
    _ = _ := pow12_131_pow z hz

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers07
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow13_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z + (131 : R) * pow13_2_mul_t z := by
  simp only [u12, pow13_2_q, f, pow13_2, pow13_2_mul_t]
  simp only [pow12_131]
  ring

theorem pow13_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_2_mul_integer z


theorem pow13_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z * u12 z = pow13_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_2_mul z


theorem pow13_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 2 = pow13_2 z := by
  calc
    _ = u12 z ^ 1 * u12 z ^ 1 := by ring
    _ = u12 z * u12 z := by simp only [pow_one]
    _ = _ := pow13_2_root z hz


theorem pow13_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z + (131 : R) * pow13_4_mul_t z := by
  simp only [pow13_2, pow13_4_q, f, pow13_4, pow13_4_mul_t]
  
  ring

theorem pow13_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_4_mul_integer z


theorem pow13_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_2 z * pow13_2 z = pow13_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_4_mul z


theorem pow13_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 4 = pow13_4 z := by
  calc
    _ = u12 z ^ 2 * u12 z ^ 2 := by ring
    _ = pow13_2 z * pow13_2 z := by rw [pow13_2_pow z hz]
    _ = _ := pow13_4_root z hz


theorem pow13_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_4 z * pow13_4 z = pow13_8_q z * f z + pow13_8 z + (131 : R) * pow13_8_mul_t z := by
  simp only [pow13_4, pow13_8_q, f, pow13_8, pow13_8_mul_t]
  
  ring

theorem pow13_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_4 z * pow13_4 z = pow13_8_q z * f z + pow13_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_8_mul_integer z


theorem pow13_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_4 z * pow13_4 z = pow13_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_8_mul z


theorem pow13_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 8 = pow13_8 z := by
  calc
    _ = u12 z ^ 4 * u12 z ^ 4 := by ring
    _ = pow13_4 z * pow13_4 z := by rw [pow13_4_pow z hz]
    _ = _ := pow13_8_root z hz


theorem pow13_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_8 z * pow13_8 z = pow13_16_q z * f z + pow13_16 z + (131 : R) * pow13_16_mul_t z := by
  simp only [pow13_8, pow13_16_q, f, pow13_16, pow13_16_mul_t]
  
  ring

theorem pow13_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_8 z * pow13_8 z = pow13_16_q z * f z + pow13_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_16_mul_integer z


theorem pow13_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_8 z * pow13_8 z = pow13_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_16_mul z


theorem pow13_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 16 = pow13_16 z := by
  calc
    _ = u12 z ^ 8 * u12 z ^ 8 := by ring
    _ = pow13_8 z * pow13_8 z := by rw [pow13_8_pow z hz]
    _ = _ := pow13_16_root z hz


theorem pow13_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_16 z * pow13_16 z = pow13_32_q z * f z + pow13_32 z + (131 : R) * pow13_32_mul_t z := by
  simp only [pow13_16, pow13_32_q, f, pow13_32, pow13_32_mul_t]
  
  ring

theorem pow13_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_16 z * pow13_16 z = pow13_32_q z * f z + pow13_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_32_mul_integer z


theorem pow13_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_16 z * pow13_16 z = pow13_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_32_mul z


theorem pow13_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 32 = pow13_32 z := by
  calc
    _ = u12 z ^ 16 * u12 z ^ 16 := by ring
    _ = pow13_16 z * pow13_16 z := by rw [pow13_16_pow z hz]
    _ = _ := pow13_32_root z hz


theorem pow13_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_32 z * pow13_32 z = pow13_64_q z * f z + pow13_64 z + (131 : R) * pow13_64_mul_t z := by
  simp only [pow13_32, pow13_64_q, f, pow13_64, pow13_64_mul_t]
  
  ring

theorem pow13_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_32 z * pow13_32 z = pow13_64_q z * f z + pow13_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_64_mul_integer z


theorem pow13_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_32 z * pow13_32 z = pow13_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_64_mul z


theorem pow13_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 64 = pow13_64 z := by
  calc
    _ = u12 z ^ 32 * u12 z ^ 32 := by ring
    _ = pow13_32 z * pow13_32 z := by rw [pow13_32_pow z hz]
    _ = _ := pow13_64_root z hz


theorem pow13_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_64 z * u12 z = pow13_65_q z * f z + pow13_65 z + (131 : R) * pow13_65_mul_t z := by
  simp only [pow13_64, u12, pow13_65_q, f, pow13_65, pow13_65_mul_t]
  simp only [pow12_131]
  ring

theorem pow13_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_64 z * u12 z = pow13_65_q z * f z + pow13_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_65_mul_integer z


theorem pow13_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_64 z * u12 z = pow13_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_65_mul z


theorem pow13_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 65 = pow13_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow13_64_pow z hz]
  exact pow13_65_root z hz


theorem pow13_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_65 z * pow13_65 z = pow13_130_q z * f z + pow13_130 z + (131 : R) * pow13_130_mul_t z := by
  simp only [pow13_65, pow13_130_q, f, pow13_130, pow13_130_mul_t]
  
  ring

theorem pow13_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_65 z * pow13_65 z = pow13_130_q z * f z + pow13_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_130_mul_integer z


theorem pow13_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_65 z * pow13_65 z = pow13_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_130_mul z


theorem pow13_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 130 = pow13_130 z := by
  calc
    _ = u12 z ^ 65 * u12 z ^ 65 := by ring
    _ = pow13_65 z * pow13_65 z := by rw [pow13_65_pow z hz]
    _ = _ := pow13_130_root z hz


theorem pow13_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_130 z * u12 z = pow13_131_q z * f z + pow13_131 z + (131 : R) * pow13_131_mul_t z := by
  simp only [pow13_130, u12, pow13_131_q, f, pow13_131, pow13_131_mul_t]
  simp only [pow12_131]
  ring

theorem pow13_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_130 z * u12 z = pow13_131_q z * f z + pow13_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_131_mul_integer z


theorem pow13_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_130 z * u12 z = pow13_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_131_mul z


theorem pow13_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 131 = pow13_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow13_130_pow z hz]
  exact pow13_131_root z hz


theorem iterate13_oai {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 13) = u13 z := by
  calc
    _ = (z ^ (131 ^ 12)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u12 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate12 z hz)
    _ = _ := pow13_131_pow z hz


end DimensionTen.Mod131

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Mod131.iterate13_oai.{u_1} := @OAI.DimensionTen.Mod131.iterate13_oai.{u_1}
