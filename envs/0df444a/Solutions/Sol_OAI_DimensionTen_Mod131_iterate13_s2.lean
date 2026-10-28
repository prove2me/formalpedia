-- Prove2me | solution 1 for OAI.DimensionTen.Mod131.iterate13_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:19:23.003338+00:00
-- url     : https://prove2.me/submissions/e3fbc52e-2be4-44a3-974a-c8f3017083de

import Mathlib
import Definitions.Def_OAIQ057D009

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Model
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem initial {R : Type*} [CommRing R] (z : R) : z ^ (131 ^ 0) = u0 z := by simp [u0]

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow1_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z + (131 : R) * pow1_2_mul_t z := by
  simp only [u0, pow1_2_q, f, pow1_2, pow1_2_mul_t]
  
  ring

theorem pow1_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_2_mul_integer z


theorem pow1_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z * u0 z = pow1_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_2_mul z


theorem pow1_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 2 = pow1_2 z := by
  calc
    _ = u0 z ^ 1 * u0 z ^ 1 := by ring
    _ = u0 z * u0 z := by simp only [pow_one]
    _ = _ := pow1_2_root z hz


theorem pow1_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z + (131 : R) * pow1_4_mul_t z := by
  simp only [pow1_2, pow1_4_q, f, pow1_4, pow1_4_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_4_mul_integer z


theorem pow1_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_2 z * pow1_2 z = pow1_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_4_mul z


theorem pow1_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 4 = pow1_4 z := by
  calc
    _ = u0 z ^ 2 * u0 z ^ 2 := by ring
    _ = pow1_2 z * pow1_2 z := by rw [pow1_2_pow z hz]
    _ = _ := pow1_4_root z hz


theorem pow1_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z + (131 : R) * pow1_8_mul_t z := by
  simp only [pow1_4, pow1_8_q, f, pow1_8, pow1_8_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_8_mul_integer z


theorem pow1_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_4 z * pow1_4 z = pow1_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_8_mul z


theorem pow1_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 8 = pow1_8 z := by
  calc
    _ = u0 z ^ 4 * u0 z ^ 4 := by ring
    _ = pow1_4 z * pow1_4 z := by rw [pow1_4_pow z hz]
    _ = _ := pow1_8_root z hz


theorem pow1_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z + (131 : R) * pow1_16_mul_t z := by
  simp only [pow1_8, pow1_16_q, f, pow1_16, pow1_16_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_16_mul_integer z


theorem pow1_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_8 z * pow1_8 z = pow1_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_16_mul z


theorem pow1_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 16 = pow1_16 z := by
  calc
    _ = u0 z ^ 8 * u0 z ^ 8 := by ring
    _ = pow1_8 z * pow1_8 z := by rw [pow1_8_pow z hz]
    _ = _ := pow1_16_root z hz


theorem pow1_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_16 z * pow1_16 z = pow1_32_q z * f z + pow1_32 z + (131 : R) * pow1_32_mul_t z := by
  simp only [pow1_16, pow1_32_q, f, pow1_32, pow1_32_mul_t]
  
  ring

theorem pow1_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_16 z * pow1_16 z = pow1_32_q z * f z + pow1_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_32_mul_integer z


theorem pow1_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_16 z * pow1_16 z = pow1_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_32_mul z


theorem pow1_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 32 = pow1_32 z := by
  calc
    _ = u0 z ^ 16 * u0 z ^ 16 := by ring
    _ = pow1_16 z * pow1_16 z := by rw [pow1_16_pow z hz]
    _ = _ := pow1_32_root z hz


theorem pow1_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_32 z * pow1_32 z = pow1_64_q z * f z + pow1_64 z + (131 : R) * pow1_64_mul_t z := by
  simp only [pow1_32, pow1_64_q, f, pow1_64, pow1_64_mul_t]
  
  ring

theorem pow1_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_32 z * pow1_32 z = pow1_64_q z * f z + pow1_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_64_mul_integer z


theorem pow1_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_32 z * pow1_32 z = pow1_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_64_mul z


theorem pow1_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 64 = pow1_64 z := by
  calc
    _ = u0 z ^ 32 * u0 z ^ 32 := by ring
    _ = pow1_32 z * pow1_32 z := by rw [pow1_32_pow z hz]
    _ = _ := pow1_64_root z hz


theorem pow1_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_64 z * u0 z = pow1_65_q z * f z + pow1_65 z + (131 : R) * pow1_65_mul_t z := by
  simp only [pow1_64, u0, pow1_65_q, f, pow1_65, pow1_65_mul_t]
  
  ring

theorem pow1_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_64 z * u0 z = pow1_65_q z * f z + pow1_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_65_mul_integer z


theorem pow1_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_64 z * u0 z = pow1_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_65_mul z


theorem pow1_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 65 = pow1_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow1_64_pow z hz]
  exact pow1_65_root z hz


theorem pow1_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_65 z * pow1_65 z = pow1_130_q z * f z + pow1_130 z + (131 : R) * pow1_130_mul_t z := by
  simp only [pow1_65, pow1_130_q, f, pow1_130, pow1_130_mul_t]
  
  ring

theorem pow1_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_65 z * pow1_65 z = pow1_130_q z * f z + pow1_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_130_mul_integer z


theorem pow1_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_65 z * pow1_65 z = pow1_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_130_mul z


theorem pow1_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 130 = pow1_130 z := by
  calc
    _ = u0 z ^ 65 * u0 z ^ 65 := by ring
    _ = pow1_65 z * pow1_65 z := by rw [pow1_65_pow z hz]
    _ = _ := pow1_130_root z hz


theorem pow1_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_130 z * u0 z = pow1_131_q z * f z + pow1_131 z + (131 : R) * pow1_131_mul_t z := by
  simp only [pow1_130, u0, pow1_131_q, f, pow1_131, pow1_131_mul_t]
  
  ring

theorem pow1_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_130 z * u0 z = pow1_131_q z * f z + pow1_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_131_mul_integer z


theorem pow1_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_130 z * u0 z = pow1_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_131_mul z


theorem pow1_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 131 = pow1_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow1_130_pow z hz]
  exact pow1_131_root z hz


theorem iterate1 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 1) = u1 z := by
  calc
    _ = (z ^ (131 ^ 0)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u0 z ^ 131 := congrArg (fun x : R => x ^ 131) (initial z )
    _ = _ := pow1_131_pow z hz


theorem pow2_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z + (131 : R) * pow2_2_mul_t z := by
  simp only [u1, pow2_2_q, f, pow2_2, pow2_2_mul_t]
  simp only [pow1_131]
  ring

theorem pow2_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_2_mul_integer z


theorem pow2_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z * u1 z = pow2_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_2_mul z


theorem pow2_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 2 = pow2_2 z := by
  calc
    _ = u1 z ^ 1 * u1 z ^ 1 := by ring
    _ = u1 z * u1 z := by simp only [pow_one]
    _ = _ := pow2_2_root z hz


theorem pow2_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z + (131 : R) * pow2_4_mul_t z := by
  simp only [pow2_2, pow2_4_q, f, pow2_4, pow2_4_mul_t]
  
  ring

theorem pow2_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_4_mul_integer z


theorem pow2_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_2 z * pow2_2 z = pow2_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_4_mul z


theorem pow2_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 4 = pow2_4 z := by
  calc
    _ = u1 z ^ 2 * u1 z ^ 2 := by ring
    _ = pow2_2 z * pow2_2 z := by rw [pow2_2_pow z hz]
    _ = _ := pow2_4_root z hz


theorem pow2_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_4 z * pow2_4 z = pow2_8_q z * f z + pow2_8 z + (131 : R) * pow2_8_mul_t z := by
  simp only [pow2_4, pow2_8_q, f, pow2_8, pow2_8_mul_t]
  
  ring

theorem pow2_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_4 z * pow2_4 z = pow2_8_q z * f z + pow2_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_8_mul_integer z


theorem pow2_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_4 z * pow2_4 z = pow2_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_8_mul z


theorem pow2_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 8 = pow2_8 z := by
  calc
    _ = u1 z ^ 4 * u1 z ^ 4 := by ring
    _ = pow2_4 z * pow2_4 z := by rw [pow2_4_pow z hz]
    _ = _ := pow2_8_root z hz


theorem pow2_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_8 z * pow2_8 z = pow2_16_q z * f z + pow2_16 z + (131 : R) * pow2_16_mul_t z := by
  simp only [pow2_8, pow2_16_q, f, pow2_16, pow2_16_mul_t]
  
  ring

theorem pow2_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_8 z * pow2_8 z = pow2_16_q z * f z + pow2_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_16_mul_integer z


theorem pow2_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_8 z * pow2_8 z = pow2_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_16_mul z


theorem pow2_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 16 = pow2_16 z := by
  calc
    _ = u1 z ^ 8 * u1 z ^ 8 := by ring
    _ = pow2_8 z * pow2_8 z := by rw [pow2_8_pow z hz]
    _ = _ := pow2_16_root z hz


theorem pow2_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_16 z * pow2_16 z = pow2_32_q z * f z + pow2_32 z + (131 : R) * pow2_32_mul_t z := by
  simp only [pow2_16, pow2_32_q, f, pow2_32, pow2_32_mul_t]
  
  ring

theorem pow2_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_16 z * pow2_16 z = pow2_32_q z * f z + pow2_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_32_mul_integer z


theorem pow2_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_16 z * pow2_16 z = pow2_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_32_mul z


theorem pow2_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 32 = pow2_32 z := by
  calc
    _ = u1 z ^ 16 * u1 z ^ 16 := by ring
    _ = pow2_16 z * pow2_16 z := by rw [pow2_16_pow z hz]
    _ = _ := pow2_32_root z hz


theorem pow2_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_32 z * pow2_32 z = pow2_64_q z * f z + pow2_64 z + (131 : R) * pow2_64_mul_t z := by
  simp only [pow2_32, pow2_64_q, f, pow2_64, pow2_64_mul_t]
  
  ring

theorem pow2_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_32 z * pow2_32 z = pow2_64_q z * f z + pow2_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_64_mul_integer z


theorem pow2_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_32 z * pow2_32 z = pow2_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_64_mul z


theorem pow2_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 64 = pow2_64 z := by
  calc
    _ = u1 z ^ 32 * u1 z ^ 32 := by ring
    _ = pow2_32 z * pow2_32 z := by rw [pow2_32_pow z hz]
    _ = _ := pow2_64_root z hz


theorem pow2_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_64 z * u1 z = pow2_65_q z * f z + pow2_65 z + (131 : R) * pow2_65_mul_t z := by
  simp only [pow2_64, u1, pow2_65_q, f, pow2_65, pow2_65_mul_t]
  simp only [pow1_131]
  ring

theorem pow2_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_64 z * u1 z = pow2_65_q z * f z + pow2_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_65_mul_integer z


theorem pow2_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_64 z * u1 z = pow2_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_65_mul z


theorem pow2_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 65 = pow2_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow2_64_pow z hz]
  exact pow2_65_root z hz


theorem pow2_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_65 z * pow2_65 z = pow2_130_q z * f z + pow2_130 z + (131 : R) * pow2_130_mul_t z := by
  simp only [pow2_65, pow2_130_q, f, pow2_130, pow2_130_mul_t]
  
  ring

theorem pow2_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_65 z * pow2_65 z = pow2_130_q z * f z + pow2_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_130_mul_integer z


theorem pow2_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_65 z * pow2_65 z = pow2_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_130_mul z


theorem pow2_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 130 = pow2_130 z := by
  calc
    _ = u1 z ^ 65 * u1 z ^ 65 := by ring
    _ = pow2_65 z * pow2_65 z := by rw [pow2_65_pow z hz]
    _ = _ := pow2_130_root z hz


theorem pow2_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_130 z * u1 z = pow2_131_q z * f z + pow2_131 z + (131 : R) * pow2_131_mul_t z := by
  simp only [pow2_130, u1, pow2_131_q, f, pow2_131, pow2_131_mul_t]
  simp only [pow1_131]
  ring

theorem pow2_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_130 z * u1 z = pow2_131_q z * f z + pow2_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_131_mul_integer z


theorem pow2_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_130 z * u1 z = pow2_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_131_mul z


theorem pow2_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 131 = pow2_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow2_130_pow z hz]
  exact pow2_131_root z hz


theorem iterate2 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 2) = u2 z := by
  calc
    _ = (z ^ (131 ^ 1)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u1 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate1 z hz)
    _ = _ := pow2_131_pow z hz

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers02
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow3_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z + (131 : R) * pow3_2_mul_t z := by
  simp only [u2, pow3_2_q, f, pow3_2, pow3_2_mul_t]
  simp only [pow2_131]
  ring

theorem pow3_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_2_mul_integer z


theorem pow3_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z * u2 z = pow3_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_2_mul z


theorem pow3_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 2 = pow3_2 z := by
  calc
    _ = u2 z ^ 1 * u2 z ^ 1 := by ring
    _ = u2 z * u2 z := by simp only [pow_one]
    _ = _ := pow3_2_root z hz


theorem pow3_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z + (131 : R) * pow3_4_mul_t z := by
  simp only [pow3_2, pow3_4_q, f, pow3_4, pow3_4_mul_t]
  
  ring

theorem pow3_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_4_mul_integer z


theorem pow3_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_2 z * pow3_2 z = pow3_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_4_mul z


theorem pow3_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 4 = pow3_4 z := by
  calc
    _ = u2 z ^ 2 * u2 z ^ 2 := by ring
    _ = pow3_2 z * pow3_2 z := by rw [pow3_2_pow z hz]
    _ = _ := pow3_4_root z hz


theorem pow3_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_4 z * pow3_4 z = pow3_8_q z * f z + pow3_8 z + (131 : R) * pow3_8_mul_t z := by
  simp only [pow3_4, pow3_8_q, f, pow3_8, pow3_8_mul_t]
  
  ring

theorem pow3_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_4 z * pow3_4 z = pow3_8_q z * f z + pow3_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_8_mul_integer z


theorem pow3_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_4 z * pow3_4 z = pow3_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_8_mul z


theorem pow3_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 8 = pow3_8 z := by
  calc
    _ = u2 z ^ 4 * u2 z ^ 4 := by ring
    _ = pow3_4 z * pow3_4 z := by rw [pow3_4_pow z hz]
    _ = _ := pow3_8_root z hz


theorem pow3_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_8 z * pow3_8 z = pow3_16_q z * f z + pow3_16 z + (131 : R) * pow3_16_mul_t z := by
  simp only [pow3_8, pow3_16_q, f, pow3_16, pow3_16_mul_t]
  
  ring

theorem pow3_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_8 z * pow3_8 z = pow3_16_q z * f z + pow3_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_16_mul_integer z


theorem pow3_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_8 z * pow3_8 z = pow3_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_16_mul z


theorem pow3_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 16 = pow3_16 z := by
  calc
    _ = u2 z ^ 8 * u2 z ^ 8 := by ring
    _ = pow3_8 z * pow3_8 z := by rw [pow3_8_pow z hz]
    _ = _ := pow3_16_root z hz


theorem pow3_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_16 z * pow3_16 z = pow3_32_q z * f z + pow3_32 z + (131 : R) * pow3_32_mul_t z := by
  simp only [pow3_16, pow3_32_q, f, pow3_32, pow3_32_mul_t]
  
  ring

theorem pow3_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_16 z * pow3_16 z = pow3_32_q z * f z + pow3_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_32_mul_integer z


theorem pow3_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_16 z * pow3_16 z = pow3_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_32_mul z


theorem pow3_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 32 = pow3_32 z := by
  calc
    _ = u2 z ^ 16 * u2 z ^ 16 := by ring
    _ = pow3_16 z * pow3_16 z := by rw [pow3_16_pow z hz]
    _ = _ := pow3_32_root z hz


theorem pow3_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_32 z * pow3_32 z = pow3_64_q z * f z + pow3_64 z + (131 : R) * pow3_64_mul_t z := by
  simp only [pow3_32, pow3_64_q, f, pow3_64, pow3_64_mul_t]
  
  ring

theorem pow3_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_32 z * pow3_32 z = pow3_64_q z * f z + pow3_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_64_mul_integer z


theorem pow3_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_32 z * pow3_32 z = pow3_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_64_mul z


theorem pow3_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 64 = pow3_64 z := by
  calc
    _ = u2 z ^ 32 * u2 z ^ 32 := by ring
    _ = pow3_32 z * pow3_32 z := by rw [pow3_32_pow z hz]
    _ = _ := pow3_64_root z hz


theorem pow3_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_64 z * u2 z = pow3_65_q z * f z + pow3_65 z + (131 : R) * pow3_65_mul_t z := by
  simp only [pow3_64, u2, pow3_65_q, f, pow3_65, pow3_65_mul_t]
  simp only [pow2_131]
  ring

theorem pow3_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_64 z * u2 z = pow3_65_q z * f z + pow3_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_65_mul_integer z


theorem pow3_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_64 z * u2 z = pow3_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_65_mul z


theorem pow3_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 65 = pow3_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow3_64_pow z hz]
  exact pow3_65_root z hz


theorem pow3_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_65 z * pow3_65 z = pow3_130_q z * f z + pow3_130 z + (131 : R) * pow3_130_mul_t z := by
  simp only [pow3_65, pow3_130_q, f, pow3_130, pow3_130_mul_t]
  
  ring

theorem pow3_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_65 z * pow3_65 z = pow3_130_q z * f z + pow3_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_130_mul_integer z


theorem pow3_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_65 z * pow3_65 z = pow3_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_130_mul z


theorem pow3_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 130 = pow3_130 z := by
  calc
    _ = u2 z ^ 65 * u2 z ^ 65 := by ring
    _ = pow3_65 z * pow3_65 z := by rw [pow3_65_pow z hz]
    _ = _ := pow3_130_root z hz


theorem pow3_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_130 z * u2 z = pow3_131_q z * f z + pow3_131 z + (131 : R) * pow3_131_mul_t z := by
  simp only [pow3_130, u2, pow3_131_q, f, pow3_131, pow3_131_mul_t]
  simp only [pow2_131]
  ring

theorem pow3_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_130 z * u2 z = pow3_131_q z * f z + pow3_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_131_mul_integer z


theorem pow3_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_130 z * u2 z = pow3_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_131_mul z


theorem pow3_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 131 = pow3_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow3_130_pow z hz]
  exact pow3_131_root z hz


theorem iterate3 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 3) = u3 z := by
  calc
    _ = (z ^ (131 ^ 2)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u2 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate2 z hz)
    _ = _ := pow3_131_pow z hz


theorem pow4_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z + (131 : R) * pow4_2_mul_t z := by
  simp only [u3, pow4_2_q, f, pow4_2, pow4_2_mul_t]
  simp only [pow3_131]
  ring

theorem pow4_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_2_mul_integer z


theorem pow4_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z * u3 z = pow4_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_2_mul z


theorem pow4_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 2 = pow4_2 z := by
  calc
    _ = u3 z ^ 1 * u3 z ^ 1 := by ring
    _ = u3 z * u3 z := by simp only [pow_one]
    _ = _ := pow4_2_root z hz


theorem pow4_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z + (131 : R) * pow4_4_mul_t z := by
  simp only [pow4_2, pow4_4_q, f, pow4_4, pow4_4_mul_t]
  
  ring

theorem pow4_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_4_mul_integer z


theorem pow4_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_2 z * pow4_2 z = pow4_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_4_mul z


theorem pow4_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 4 = pow4_4 z := by
  calc
    _ = u3 z ^ 2 * u3 z ^ 2 := by ring
    _ = pow4_2 z * pow4_2 z := by rw [pow4_2_pow z hz]
    _ = _ := pow4_4_root z hz


theorem pow4_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_4 z * pow4_4 z = pow4_8_q z * f z + pow4_8 z + (131 : R) * pow4_8_mul_t z := by
  simp only [pow4_4, pow4_8_q, f, pow4_8, pow4_8_mul_t]
  
  ring

theorem pow4_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_4 z * pow4_4 z = pow4_8_q z * f z + pow4_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_8_mul_integer z


theorem pow4_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_4 z * pow4_4 z = pow4_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_8_mul z


theorem pow4_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 8 = pow4_8 z := by
  calc
    _ = u3 z ^ 4 * u3 z ^ 4 := by ring
    _ = pow4_4 z * pow4_4 z := by rw [pow4_4_pow z hz]
    _ = _ := pow4_8_root z hz


theorem pow4_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_8 z * pow4_8 z = pow4_16_q z * f z + pow4_16 z + (131 : R) * pow4_16_mul_t z := by
  simp only [pow4_8, pow4_16_q, f, pow4_16, pow4_16_mul_t]
  
  ring

theorem pow4_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_8 z * pow4_8 z = pow4_16_q z * f z + pow4_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_16_mul_integer z


theorem pow4_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_8 z * pow4_8 z = pow4_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_16_mul z


theorem pow4_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 16 = pow4_16 z := by
  calc
    _ = u3 z ^ 8 * u3 z ^ 8 := by ring
    _ = pow4_8 z * pow4_8 z := by rw [pow4_8_pow z hz]
    _ = _ := pow4_16_root z hz


theorem pow4_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_16 z * pow4_16 z = pow4_32_q z * f z + pow4_32 z + (131 : R) * pow4_32_mul_t z := by
  simp only [pow4_16, pow4_32_q, f, pow4_32, pow4_32_mul_t]
  
  ring

theorem pow4_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_16 z * pow4_16 z = pow4_32_q z * f z + pow4_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_32_mul_integer z


theorem pow4_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_16 z * pow4_16 z = pow4_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_32_mul z


theorem pow4_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 32 = pow4_32 z := by
  calc
    _ = u3 z ^ 16 * u3 z ^ 16 := by ring
    _ = pow4_16 z * pow4_16 z := by rw [pow4_16_pow z hz]
    _ = _ := pow4_32_root z hz


theorem pow4_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_32 z * pow4_32 z = pow4_64_q z * f z + pow4_64 z + (131 : R) * pow4_64_mul_t z := by
  simp only [pow4_32, pow4_64_q, f, pow4_64, pow4_64_mul_t]
  
  ring

theorem pow4_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_32 z * pow4_32 z = pow4_64_q z * f z + pow4_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_64_mul_integer z


theorem pow4_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_32 z * pow4_32 z = pow4_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_64_mul z


theorem pow4_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 64 = pow4_64 z := by
  calc
    _ = u3 z ^ 32 * u3 z ^ 32 := by ring
    _ = pow4_32 z * pow4_32 z := by rw [pow4_32_pow z hz]
    _ = _ := pow4_64_root z hz


theorem pow4_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_64 z * u3 z = pow4_65_q z * f z + pow4_65 z + (131 : R) * pow4_65_mul_t z := by
  simp only [pow4_64, u3, pow4_65_q, f, pow4_65, pow4_65_mul_t]
  simp only [pow3_131]
  ring

theorem pow4_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_64 z * u3 z = pow4_65_q z * f z + pow4_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_65_mul_integer z


theorem pow4_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_64 z * u3 z = pow4_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_65_mul z


theorem pow4_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 65 = pow4_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow4_64_pow z hz]
  exact pow4_65_root z hz


theorem pow4_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_65 z * pow4_65 z = pow4_130_q z * f z + pow4_130 z + (131 : R) * pow4_130_mul_t z := by
  simp only [pow4_65, pow4_130_q, f, pow4_130, pow4_130_mul_t]
  
  ring

theorem pow4_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_65 z * pow4_65 z = pow4_130_q z * f z + pow4_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_130_mul_integer z


theorem pow4_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_65 z * pow4_65 z = pow4_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_130_mul z


theorem pow4_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 130 = pow4_130 z := by
  calc
    _ = u3 z ^ 65 * u3 z ^ 65 := by ring
    _ = pow4_65 z * pow4_65 z := by rw [pow4_65_pow z hz]
    _ = _ := pow4_130_root z hz


theorem pow4_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_130 z * u3 z = pow4_131_q z * f z + pow4_131 z + (131 : R) * pow4_131_mul_t z := by
  simp only [pow4_130, u3, pow4_131_q, f, pow4_131, pow4_131_mul_t]
  simp only [pow3_131]
  ring

theorem pow4_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_130 z * u3 z = pow4_131_q z * f z + pow4_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_131_mul_integer z


theorem pow4_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_130 z * u3 z = pow4_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_131_mul z


theorem pow4_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 131 = pow4_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow4_130_pow z hz]
  exact pow4_131_root z hz


theorem iterate4 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 4) = u4 z := by
  calc
    _ = (z ^ (131 ^ 3)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u3 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate3 z hz)
    _ = _ := pow4_131_pow z hz

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers03
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow5_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z + (131 : R) * pow5_2_mul_t z := by
  simp only [u4, pow5_2_q, f, pow5_2, pow5_2_mul_t]
  simp only [pow4_131]
  ring

theorem pow5_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_2_mul_integer z


theorem pow5_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z * u4 z = pow5_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_2_mul z


theorem pow5_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 2 = pow5_2 z := by
  calc
    _ = u4 z ^ 1 * u4 z ^ 1 := by ring
    _ = u4 z * u4 z := by simp only [pow_one]
    _ = _ := pow5_2_root z hz


theorem pow5_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z + (131 : R) * pow5_4_mul_t z := by
  simp only [pow5_2, pow5_4_q, f, pow5_4, pow5_4_mul_t]
  
  ring

theorem pow5_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_4_mul_integer z


theorem pow5_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_2 z * pow5_2 z = pow5_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_4_mul z


theorem pow5_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 4 = pow5_4 z := by
  calc
    _ = u4 z ^ 2 * u4 z ^ 2 := by ring
    _ = pow5_2 z * pow5_2 z := by rw [pow5_2_pow z hz]
    _ = _ := pow5_4_root z hz


theorem pow5_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_4 z * pow5_4 z = pow5_8_q z * f z + pow5_8 z + (131 : R) * pow5_8_mul_t z := by
  simp only [pow5_4, pow5_8_q, f, pow5_8, pow5_8_mul_t]
  
  ring

theorem pow5_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_4 z * pow5_4 z = pow5_8_q z * f z + pow5_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_8_mul_integer z


theorem pow5_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_4 z * pow5_4 z = pow5_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_8_mul z


theorem pow5_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 8 = pow5_8 z := by
  calc
    _ = u4 z ^ 4 * u4 z ^ 4 := by ring
    _ = pow5_4 z * pow5_4 z := by rw [pow5_4_pow z hz]
    _ = _ := pow5_8_root z hz


theorem pow5_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_8 z * pow5_8 z = pow5_16_q z * f z + pow5_16 z + (131 : R) * pow5_16_mul_t z := by
  simp only [pow5_8, pow5_16_q, f, pow5_16, pow5_16_mul_t]
  
  ring

theorem pow5_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_8 z * pow5_8 z = pow5_16_q z * f z + pow5_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_16_mul_integer z


theorem pow5_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_8 z * pow5_8 z = pow5_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_16_mul z


theorem pow5_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 16 = pow5_16 z := by
  calc
    _ = u4 z ^ 8 * u4 z ^ 8 := by ring
    _ = pow5_8 z * pow5_8 z := by rw [pow5_8_pow z hz]
    _ = _ := pow5_16_root z hz


theorem pow5_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_16 z * pow5_16 z = pow5_32_q z * f z + pow5_32 z + (131 : R) * pow5_32_mul_t z := by
  simp only [pow5_16, pow5_32_q, f, pow5_32, pow5_32_mul_t]
  
  ring

theorem pow5_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_16 z * pow5_16 z = pow5_32_q z * f z + pow5_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_32_mul_integer z


theorem pow5_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_16 z * pow5_16 z = pow5_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_32_mul z


theorem pow5_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 32 = pow5_32 z := by
  calc
    _ = u4 z ^ 16 * u4 z ^ 16 := by ring
    _ = pow5_16 z * pow5_16 z := by rw [pow5_16_pow z hz]
    _ = _ := pow5_32_root z hz


theorem pow5_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_32 z * pow5_32 z = pow5_64_q z * f z + pow5_64 z + (131 : R) * pow5_64_mul_t z := by
  simp only [pow5_32, pow5_64_q, f, pow5_64, pow5_64_mul_t]
  
  ring

theorem pow5_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_32 z * pow5_32 z = pow5_64_q z * f z + pow5_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_64_mul_integer z


theorem pow5_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_32 z * pow5_32 z = pow5_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_64_mul z


theorem pow5_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 64 = pow5_64 z := by
  calc
    _ = u4 z ^ 32 * u4 z ^ 32 := by ring
    _ = pow5_32 z * pow5_32 z := by rw [pow5_32_pow z hz]
    _ = _ := pow5_64_root z hz


theorem pow5_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_64 z * u4 z = pow5_65_q z * f z + pow5_65 z + (131 : R) * pow5_65_mul_t z := by
  simp only [pow5_64, u4, pow5_65_q, f, pow5_65, pow5_65_mul_t]
  simp only [pow4_131]
  ring

theorem pow5_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_64 z * u4 z = pow5_65_q z * f z + pow5_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_65_mul_integer z


theorem pow5_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_64 z * u4 z = pow5_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_65_mul z


theorem pow5_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 65 = pow5_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow5_64_pow z hz]
  exact pow5_65_root z hz


theorem pow5_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_65 z * pow5_65 z = pow5_130_q z * f z + pow5_130 z + (131 : R) * pow5_130_mul_t z := by
  simp only [pow5_65, pow5_130_q, f, pow5_130, pow5_130_mul_t]
  
  ring

theorem pow5_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_65 z * pow5_65 z = pow5_130_q z * f z + pow5_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_130_mul_integer z


theorem pow5_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_65 z * pow5_65 z = pow5_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_130_mul z


theorem pow5_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 130 = pow5_130 z := by
  calc
    _ = u4 z ^ 65 * u4 z ^ 65 := by ring
    _ = pow5_65 z * pow5_65 z := by rw [pow5_65_pow z hz]
    _ = _ := pow5_130_root z hz


theorem pow5_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_130 z * u4 z = pow5_131_q z * f z + pow5_131 z + (131 : R) * pow5_131_mul_t z := by
  simp only [pow5_130, u4, pow5_131_q, f, pow5_131, pow5_131_mul_t]
  simp only [pow4_131]
  ring

theorem pow5_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_130 z * u4 z = pow5_131_q z * f z + pow5_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_131_mul_integer z


theorem pow5_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_130 z * u4 z = pow5_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_131_mul z


theorem pow5_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 131 = pow5_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow5_130_pow z hz]
  exact pow5_131_root z hz


theorem iterate5 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 5) = u5 z := by
  calc
    _ = (z ^ (131 ^ 4)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u4 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate4 z hz)
    _ = _ := pow5_131_pow z hz


theorem pow6_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z + (131 : R) * pow6_2_mul_t z := by
  simp only [u5, pow6_2_q, f, pow6_2, pow6_2_mul_t]
  simp only [pow5_131]
  ring

theorem pow6_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_2_mul_integer z


theorem pow6_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z * u5 z = pow6_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_2_mul z


theorem pow6_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 2 = pow6_2 z := by
  calc
    _ = u5 z ^ 1 * u5 z ^ 1 := by ring
    _ = u5 z * u5 z := by simp only [pow_one]
    _ = _ := pow6_2_root z hz


theorem pow6_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z + (131 : R) * pow6_4_mul_t z := by
  simp only [pow6_2, pow6_4_q, f, pow6_4, pow6_4_mul_t]
  
  ring

theorem pow6_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_4_mul_integer z


theorem pow6_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_2 z * pow6_2 z = pow6_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_4_mul z


theorem pow6_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 4 = pow6_4 z := by
  calc
    _ = u5 z ^ 2 * u5 z ^ 2 := by ring
    _ = pow6_2 z * pow6_2 z := by rw [pow6_2_pow z hz]
    _ = _ := pow6_4_root z hz


theorem pow6_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_4 z * pow6_4 z = pow6_8_q z * f z + pow6_8 z + (131 : R) * pow6_8_mul_t z := by
  simp only [pow6_4, pow6_8_q, f, pow6_8, pow6_8_mul_t]
  
  ring

theorem pow6_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_4 z * pow6_4 z = pow6_8_q z * f z + pow6_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_8_mul_integer z


theorem pow6_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_4 z * pow6_4 z = pow6_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_8_mul z


theorem pow6_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 8 = pow6_8 z := by
  calc
    _ = u5 z ^ 4 * u5 z ^ 4 := by ring
    _ = pow6_4 z * pow6_4 z := by rw [pow6_4_pow z hz]
    _ = _ := pow6_8_root z hz


theorem pow6_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_8 z * pow6_8 z = pow6_16_q z * f z + pow6_16 z + (131 : R) * pow6_16_mul_t z := by
  simp only [pow6_8, pow6_16_q, f, pow6_16, pow6_16_mul_t]
  
  ring

theorem pow6_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_8 z * pow6_8 z = pow6_16_q z * f z + pow6_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_16_mul_integer z


theorem pow6_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_8 z * pow6_8 z = pow6_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_16_mul z


theorem pow6_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 16 = pow6_16 z := by
  calc
    _ = u5 z ^ 8 * u5 z ^ 8 := by ring
    _ = pow6_8 z * pow6_8 z := by rw [pow6_8_pow z hz]
    _ = _ := pow6_16_root z hz


theorem pow6_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_16 z * pow6_16 z = pow6_32_q z * f z + pow6_32 z + (131 : R) * pow6_32_mul_t z := by
  simp only [pow6_16, pow6_32_q, f, pow6_32, pow6_32_mul_t]
  
  ring

theorem pow6_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_16 z * pow6_16 z = pow6_32_q z * f z + pow6_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_32_mul_integer z


theorem pow6_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_16 z * pow6_16 z = pow6_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_32_mul z


theorem pow6_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 32 = pow6_32 z := by
  calc
    _ = u5 z ^ 16 * u5 z ^ 16 := by ring
    _ = pow6_16 z * pow6_16 z := by rw [pow6_16_pow z hz]
    _ = _ := pow6_32_root z hz


theorem pow6_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_32 z * pow6_32 z = pow6_64_q z * f z + pow6_64 z + (131 : R) * pow6_64_mul_t z := by
  simp only [pow6_32, pow6_64_q, f, pow6_64, pow6_64_mul_t]
  
  ring

theorem pow6_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_32 z * pow6_32 z = pow6_64_q z * f z + pow6_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_64_mul_integer z


theorem pow6_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_32 z * pow6_32 z = pow6_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_64_mul z


theorem pow6_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 64 = pow6_64 z := by
  calc
    _ = u5 z ^ 32 * u5 z ^ 32 := by ring
    _ = pow6_32 z * pow6_32 z := by rw [pow6_32_pow z hz]
    _ = _ := pow6_64_root z hz


theorem pow6_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_64 z * u5 z = pow6_65_q z * f z + pow6_65 z + (131 : R) * pow6_65_mul_t z := by
  simp only [pow6_64, u5, pow6_65_q, f, pow6_65, pow6_65_mul_t]
  simp only [pow5_131]
  ring

theorem pow6_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_64 z * u5 z = pow6_65_q z * f z + pow6_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_65_mul_integer z


theorem pow6_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_64 z * u5 z = pow6_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_65_mul z


theorem pow6_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 65 = pow6_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow6_64_pow z hz]
  exact pow6_65_root z hz


theorem pow6_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_65 z * pow6_65 z = pow6_130_q z * f z + pow6_130 z + (131 : R) * pow6_130_mul_t z := by
  simp only [pow6_65, pow6_130_q, f, pow6_130, pow6_130_mul_t]
  
  ring

theorem pow6_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_65 z * pow6_65 z = pow6_130_q z * f z + pow6_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_130_mul_integer z


theorem pow6_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_65 z * pow6_65 z = pow6_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_130_mul z


theorem pow6_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 130 = pow6_130 z := by
  calc
    _ = u5 z ^ 65 * u5 z ^ 65 := by ring
    _ = pow6_65 z * pow6_65 z := by rw [pow6_65_pow z hz]
    _ = _ := pow6_130_root z hz


theorem pow6_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_130 z * u5 z = pow6_131_q z * f z + pow6_131 z + (131 : R) * pow6_131_mul_t z := by
  simp only [pow6_130, u5, pow6_131_q, f, pow6_131, pow6_131_mul_t]
  simp only [pow5_131]
  ring

theorem pow6_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_130 z * u5 z = pow6_131_q z * f z + pow6_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_131_mul_integer z


theorem pow6_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_130 z * u5 z = pow6_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_131_mul z


theorem pow6_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 131 = pow6_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow6_130_pow z hz]
  exact pow6_131_root z hz


theorem iterate6 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 6) = u6 z := by
  calc
    _ = (z ^ (131 ^ 5)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u5 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate5 z hz)
    _ = _ := pow6_131_pow z hz

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers04
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow7_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z + (131 : R) * pow7_2_mul_t z := by
  simp only [u6, pow7_2_q, f, pow7_2, pow7_2_mul_t]
  simp only [pow6_131]
  ring

theorem pow7_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_2_mul_integer z


theorem pow7_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z * u6 z = pow7_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_2_mul z


theorem pow7_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 2 = pow7_2 z := by
  calc
    _ = u6 z ^ 1 * u6 z ^ 1 := by ring
    _ = u6 z * u6 z := by simp only [pow_one]
    _ = _ := pow7_2_root z hz


theorem pow7_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z + (131 : R) * pow7_4_mul_t z := by
  simp only [pow7_2, pow7_4_q, f, pow7_4, pow7_4_mul_t]
  
  ring

theorem pow7_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_4_mul_integer z


theorem pow7_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_2 z * pow7_2 z = pow7_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_4_mul z


theorem pow7_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 4 = pow7_4 z := by
  calc
    _ = u6 z ^ 2 * u6 z ^ 2 := by ring
    _ = pow7_2 z * pow7_2 z := by rw [pow7_2_pow z hz]
    _ = _ := pow7_4_root z hz


theorem pow7_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_4 z * pow7_4 z = pow7_8_q z * f z + pow7_8 z + (131 : R) * pow7_8_mul_t z := by
  simp only [pow7_4, pow7_8_q, f, pow7_8, pow7_8_mul_t]
  
  ring

theorem pow7_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_4 z * pow7_4 z = pow7_8_q z * f z + pow7_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_8_mul_integer z


theorem pow7_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_4 z * pow7_4 z = pow7_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_8_mul z


theorem pow7_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 8 = pow7_8 z := by
  calc
    _ = u6 z ^ 4 * u6 z ^ 4 := by ring
    _ = pow7_4 z * pow7_4 z := by rw [pow7_4_pow z hz]
    _ = _ := pow7_8_root z hz


theorem pow7_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_8 z * pow7_8 z = pow7_16_q z * f z + pow7_16 z + (131 : R) * pow7_16_mul_t z := by
  simp only [pow7_8, pow7_16_q, f, pow7_16, pow7_16_mul_t]
  
  ring

theorem pow7_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_8 z * pow7_8 z = pow7_16_q z * f z + pow7_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_16_mul_integer z


theorem pow7_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_8 z * pow7_8 z = pow7_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_16_mul z


theorem pow7_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 16 = pow7_16 z := by
  calc
    _ = u6 z ^ 8 * u6 z ^ 8 := by ring
    _ = pow7_8 z * pow7_8 z := by rw [pow7_8_pow z hz]
    _ = _ := pow7_16_root z hz


theorem pow7_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_16 z * pow7_16 z = pow7_32_q z * f z + pow7_32 z + (131 : R) * pow7_32_mul_t z := by
  simp only [pow7_16, pow7_32_q, f, pow7_32, pow7_32_mul_t]
  
  ring

theorem pow7_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_16 z * pow7_16 z = pow7_32_q z * f z + pow7_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_32_mul_integer z


theorem pow7_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_16 z * pow7_16 z = pow7_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_32_mul z


theorem pow7_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 32 = pow7_32 z := by
  calc
    _ = u6 z ^ 16 * u6 z ^ 16 := by ring
    _ = pow7_16 z * pow7_16 z := by rw [pow7_16_pow z hz]
    _ = _ := pow7_32_root z hz


theorem pow7_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_32 z * pow7_32 z = pow7_64_q z * f z + pow7_64 z + (131 : R) * pow7_64_mul_t z := by
  simp only [pow7_32, pow7_64_q, f, pow7_64, pow7_64_mul_t]
  
  ring

theorem pow7_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_32 z * pow7_32 z = pow7_64_q z * f z + pow7_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_64_mul_integer z


theorem pow7_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_32 z * pow7_32 z = pow7_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_64_mul z


theorem pow7_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 64 = pow7_64 z := by
  calc
    _ = u6 z ^ 32 * u6 z ^ 32 := by ring
    _ = pow7_32 z * pow7_32 z := by rw [pow7_32_pow z hz]
    _ = _ := pow7_64_root z hz


theorem pow7_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_64 z * u6 z = pow7_65_q z * f z + pow7_65 z + (131 : R) * pow7_65_mul_t z := by
  simp only [pow7_64, u6, pow7_65_q, f, pow7_65, pow7_65_mul_t]
  simp only [pow6_131]
  ring

theorem pow7_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_64 z * u6 z = pow7_65_q z * f z + pow7_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_65_mul_integer z


theorem pow7_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_64 z * u6 z = pow7_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_65_mul z


theorem pow7_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 65 = pow7_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow7_64_pow z hz]
  exact pow7_65_root z hz


theorem pow7_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_65 z * pow7_65 z = pow7_130_q z * f z + pow7_130 z + (131 : R) * pow7_130_mul_t z := by
  simp only [pow7_65, pow7_130_q, f, pow7_130, pow7_130_mul_t]
  
  ring

theorem pow7_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_65 z * pow7_65 z = pow7_130_q z * f z + pow7_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_130_mul_integer z


theorem pow7_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_65 z * pow7_65 z = pow7_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_130_mul z


theorem pow7_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 130 = pow7_130 z := by
  calc
    _ = u6 z ^ 65 * u6 z ^ 65 := by ring
    _ = pow7_65 z * pow7_65 z := by rw [pow7_65_pow z hz]
    _ = _ := pow7_130_root z hz


theorem pow7_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_130 z * u6 z = pow7_131_q z * f z + pow7_131 z + (131 : R) * pow7_131_mul_t z := by
  simp only [pow7_130, u6, pow7_131_q, f, pow7_131, pow7_131_mul_t]
  simp only [pow6_131]
  ring

theorem pow7_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_130 z * u6 z = pow7_131_q z * f z + pow7_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_131_mul_integer z


theorem pow7_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_130 z * u6 z = pow7_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_131_mul z


theorem pow7_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 131 = pow7_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow7_130_pow z hz]
  exact pow7_131_root z hz


theorem iterate7 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 7) = u7 z := by
  calc
    _ = (z ^ (131 ^ 6)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u6 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate6 z hz)
    _ = _ := pow7_131_pow z hz


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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers05
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers06
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers07
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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


theorem iterate13_s2_oai {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 13) = u13 z := by
  calc
    _ = (z ^ (131 ^ 12)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u12 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate12 z hz)
    _ = _ := pow13_131_pow z hz


end DimensionTen.Mod131

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Mod131.iterate13_s2_oai.{u_1} := @OAI.DimensionTen.Mod131.iterate13_s2_oai.{u_1}
