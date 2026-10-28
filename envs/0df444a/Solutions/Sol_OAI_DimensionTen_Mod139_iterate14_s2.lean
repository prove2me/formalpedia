-- Prove2me | solution 1 for OAI.DimensionTen.Mod139.iterate14_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:56:57.181992+00:00
-- url     : https://prove2.me/submissions/d4ff8730-2255-4101-923b-6f83be30af56

import Mathlib
import Definitions.Def_OAIQ057D009

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Model
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem initial {R : Type*} [CommRing R] (z : R) : z ^ (139 ^ 0) = u0 z := by simp [u0]

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow1_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z + (139 : R) * pow1_2_mul_t z := by
  simp only [u0, pow1_2_q, f, pow1_2, pow1_2_mul_t]
  
  ring

theorem pow1_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_2_mul_integer z


theorem pow1_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z * u0 z = pow1_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_2_mul z


theorem pow1_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 2 = pow1_2 z := by
  calc
    _ = u0 z ^ 1 * u0 z ^ 1 := by ring
    _ = u0 z * u0 z := by simp only [pow_one]
    _ = _ := pow1_2_root z hz


theorem pow1_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z + (139 : R) * pow1_4_mul_t z := by
  simp only [pow1_2, pow1_4_q, f, pow1_4, pow1_4_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_4_mul_integer z


theorem pow1_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_2 z * pow1_2 z = pow1_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_4_mul z


theorem pow1_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 4 = pow1_4 z := by
  calc
    _ = u0 z ^ 2 * u0 z ^ 2 := by ring
    _ = pow1_2 z * pow1_2 z := by rw [pow1_2_pow z hz]
    _ = _ := pow1_4_root z hz


theorem pow1_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z + (139 : R) * pow1_8_mul_t z := by
  simp only [pow1_4, pow1_8_q, f, pow1_8, pow1_8_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_8_mul_integer z


theorem pow1_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_4 z * pow1_4 z = pow1_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_8_mul z


theorem pow1_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 8 = pow1_8 z := by
  calc
    _ = u0 z ^ 4 * u0 z ^ 4 := by ring
    _ = pow1_4 z * pow1_4 z := by rw [pow1_4_pow z hz]
    _ = _ := pow1_8_root z hz


theorem pow1_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z + (139 : R) * pow1_16_mul_t z := by
  simp only [pow1_8, pow1_16_q, f, pow1_16, pow1_16_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_16_mul_integer z


theorem pow1_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_8 z * pow1_8 z = pow1_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_16_mul z


theorem pow1_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 16 = pow1_16 z := by
  calc
    _ = u0 z ^ 8 * u0 z ^ 8 := by ring
    _ = pow1_8 z * pow1_8 z := by rw [pow1_8_pow z hz]
    _ = _ := pow1_16_root z hz


theorem pow1_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_16 z * u0 z = pow1_17_q z * f z + pow1_17 z + (139 : R) * pow1_17_mul_t z := by
  simp only [pow1_16, u0, pow1_17_q, f, pow1_17, pow1_17_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_16 z * u0 z = pow1_17_q z * f z + pow1_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_17_mul_integer z


theorem pow1_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_16 z * u0 z = pow1_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_17_mul z


theorem pow1_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 17 = pow1_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow1_16_pow z hz]
  exact pow1_17_root z hz


theorem pow1_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_17 z * pow1_17 z = pow1_34_q z * f z + pow1_34 z + (139 : R) * pow1_34_mul_t z := by
  simp only [pow1_17, pow1_34_q, f, pow1_34, pow1_34_mul_t]
  
  ring

theorem pow1_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_17 z * pow1_17 z = pow1_34_q z * f z + pow1_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_34_mul_integer z


theorem pow1_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_17 z * pow1_17 z = pow1_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_34_mul z


theorem pow1_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 34 = pow1_34 z := by
  calc
    _ = u0 z ^ 17 * u0 z ^ 17 := by ring
    _ = pow1_17 z * pow1_17 z := by rw [pow1_17_pow z hz]
    _ = _ := pow1_34_root z hz


theorem pow1_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_34 z * pow1_34 z = pow1_68_q z * f z + pow1_68 z + (139 : R) * pow1_68_mul_t z := by
  simp only [pow1_34, pow1_68_q, f, pow1_68, pow1_68_mul_t]
  
  ring

theorem pow1_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_34 z * pow1_34 z = pow1_68_q z * f z + pow1_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_68_mul_integer z


theorem pow1_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_34 z * pow1_34 z = pow1_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_68_mul z


theorem pow1_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 68 = pow1_68 z := by
  calc
    _ = u0 z ^ 34 * u0 z ^ 34 := by ring
    _ = pow1_34 z * pow1_34 z := by rw [pow1_34_pow z hz]
    _ = _ := pow1_68_root z hz


theorem pow1_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_68 z * u0 z = pow1_69_q z * f z + pow1_69 z + (139 : R) * pow1_69_mul_t z := by
  simp only [pow1_68, u0, pow1_69_q, f, pow1_69, pow1_69_mul_t]
  
  ring

theorem pow1_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_68 z * u0 z = pow1_69_q z * f z + pow1_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_69_mul_integer z


theorem pow1_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_68 z * u0 z = pow1_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_69_mul z


theorem pow1_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 69 = pow1_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow1_68_pow z hz]
  exact pow1_69_root z hz


theorem pow1_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_69 z * pow1_69 z = pow1_138_q z * f z + pow1_138 z + (139 : R) * pow1_138_mul_t z := by
  simp only [pow1_69, pow1_138_q, f, pow1_138, pow1_138_mul_t]
  
  ring

theorem pow1_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_69 z * pow1_69 z = pow1_138_q z * f z + pow1_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_138_mul_integer z


theorem pow1_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_69 z * pow1_69 z = pow1_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_138_mul z


theorem pow1_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 138 = pow1_138 z := by
  calc
    _ = u0 z ^ 69 * u0 z ^ 69 := by ring
    _ = pow1_69 z * pow1_69 z := by rw [pow1_69_pow z hz]
    _ = _ := pow1_138_root z hz


theorem pow1_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_138 z * u0 z = pow1_139_q z * f z + pow1_139 z + (139 : R) * pow1_139_mul_t z := by
  simp only [pow1_138, u0, pow1_139_q, f, pow1_139, pow1_139_mul_t]
  
  ring

theorem pow1_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_138 z * u0 z = pow1_139_q z * f z + pow1_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_139_mul_integer z


theorem pow1_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_138 z * u0 z = pow1_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_139_mul z


theorem pow1_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 139 = pow1_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow1_138_pow z hz]
  exact pow1_139_root z hz


theorem iterate1 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 1) = u1 z := by
  calc
    _ = (z ^ (139 ^ 0)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u0 z ^ 139 := congrArg (fun x : R => x ^ 139) (initial z )
    _ = _ := pow1_139_pow z hz


theorem pow2_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z + (139 : R) * pow2_2_mul_t z := by
  simp only [u1, pow2_2_q, f, pow2_2, pow2_2_mul_t]
  simp only [pow1_139]
  ring

theorem pow2_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_2_mul_integer z


theorem pow2_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z * u1 z = pow2_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_2_mul z


theorem pow2_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 2 = pow2_2 z := by
  calc
    _ = u1 z ^ 1 * u1 z ^ 1 := by ring
    _ = u1 z * u1 z := by simp only [pow_one]
    _ = _ := pow2_2_root z hz


theorem pow2_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z + (139 : R) * pow2_4_mul_t z := by
  simp only [pow2_2, pow2_4_q, f, pow2_4, pow2_4_mul_t]
  
  ring

theorem pow2_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_4_mul_integer z


theorem pow2_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_2 z * pow2_2 z = pow2_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_4_mul z


theorem pow2_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 4 = pow2_4 z := by
  calc
    _ = u1 z ^ 2 * u1 z ^ 2 := by ring
    _ = pow2_2 z * pow2_2 z := by rw [pow2_2_pow z hz]
    _ = _ := pow2_4_root z hz


theorem pow2_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_4 z * pow2_4 z = pow2_8_q z * f z + pow2_8 z + (139 : R) * pow2_8_mul_t z := by
  simp only [pow2_4, pow2_8_q, f, pow2_8, pow2_8_mul_t]
  
  ring

theorem pow2_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_4 z * pow2_4 z = pow2_8_q z * f z + pow2_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_8_mul_integer z


theorem pow2_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_4 z * pow2_4 z = pow2_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_8_mul z


theorem pow2_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 8 = pow2_8 z := by
  calc
    _ = u1 z ^ 4 * u1 z ^ 4 := by ring
    _ = pow2_4 z * pow2_4 z := by rw [pow2_4_pow z hz]
    _ = _ := pow2_8_root z hz


theorem pow2_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_8 z * pow2_8 z = pow2_16_q z * f z + pow2_16 z + (139 : R) * pow2_16_mul_t z := by
  simp only [pow2_8, pow2_16_q, f, pow2_16, pow2_16_mul_t]
  
  ring

theorem pow2_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_8 z * pow2_8 z = pow2_16_q z * f z + pow2_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_16_mul_integer z


theorem pow2_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_8 z * pow2_8 z = pow2_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_16_mul z


theorem pow2_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 16 = pow2_16 z := by
  calc
    _ = u1 z ^ 8 * u1 z ^ 8 := by ring
    _ = pow2_8 z * pow2_8 z := by rw [pow2_8_pow z hz]
    _ = _ := pow2_16_root z hz


theorem pow2_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_16 z * u1 z = pow2_17_q z * f z + pow2_17 z + (139 : R) * pow2_17_mul_t z := by
  simp only [pow2_16, u1, pow2_17_q, f, pow2_17, pow2_17_mul_t]
  simp only [pow1_139]
  ring

theorem pow2_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_16 z * u1 z = pow2_17_q z * f z + pow2_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_17_mul_integer z


theorem pow2_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_16 z * u1 z = pow2_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_17_mul z


theorem pow2_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 17 = pow2_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow2_16_pow z hz]
  exact pow2_17_root z hz


theorem pow2_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_17 z * pow2_17 z = pow2_34_q z * f z + pow2_34 z + (139 : R) * pow2_34_mul_t z := by
  simp only [pow2_17, pow2_34_q, f, pow2_34, pow2_34_mul_t]
  
  ring

theorem pow2_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_17 z * pow2_17 z = pow2_34_q z * f z + pow2_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_34_mul_integer z


theorem pow2_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_17 z * pow2_17 z = pow2_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_34_mul z


theorem pow2_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 34 = pow2_34 z := by
  calc
    _ = u1 z ^ 17 * u1 z ^ 17 := by ring
    _ = pow2_17 z * pow2_17 z := by rw [pow2_17_pow z hz]
    _ = _ := pow2_34_root z hz


theorem pow2_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_34 z * pow2_34 z = pow2_68_q z * f z + pow2_68 z + (139 : R) * pow2_68_mul_t z := by
  simp only [pow2_34, pow2_68_q, f, pow2_68, pow2_68_mul_t]
  
  ring

theorem pow2_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_34 z * pow2_34 z = pow2_68_q z * f z + pow2_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_68_mul_integer z


theorem pow2_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_34 z * pow2_34 z = pow2_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_68_mul z


theorem pow2_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 68 = pow2_68 z := by
  calc
    _ = u1 z ^ 34 * u1 z ^ 34 := by ring
    _ = pow2_34 z * pow2_34 z := by rw [pow2_34_pow z hz]
    _ = _ := pow2_68_root z hz


theorem pow2_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_68 z * u1 z = pow2_69_q z * f z + pow2_69 z + (139 : R) * pow2_69_mul_t z := by
  simp only [pow2_68, u1, pow2_69_q, f, pow2_69, pow2_69_mul_t]
  simp only [pow1_139]
  ring

theorem pow2_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_68 z * u1 z = pow2_69_q z * f z + pow2_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_69_mul_integer z


theorem pow2_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_68 z * u1 z = pow2_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_69_mul z


theorem pow2_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 69 = pow2_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow2_68_pow z hz]
  exact pow2_69_root z hz


theorem pow2_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_69 z * pow2_69 z = pow2_138_q z * f z + pow2_138 z + (139 : R) * pow2_138_mul_t z := by
  simp only [pow2_69, pow2_138_q, f, pow2_138, pow2_138_mul_t]
  
  ring

theorem pow2_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_69 z * pow2_69 z = pow2_138_q z * f z + pow2_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_138_mul_integer z


theorem pow2_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_69 z * pow2_69 z = pow2_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_138_mul z


theorem pow2_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 138 = pow2_138 z := by
  calc
    _ = u1 z ^ 69 * u1 z ^ 69 := by ring
    _ = pow2_69 z * pow2_69 z := by rw [pow2_69_pow z hz]
    _ = _ := pow2_138_root z hz


theorem pow2_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_138 z * u1 z = pow2_139_q z * f z + pow2_139 z + (139 : R) * pow2_139_mul_t z := by
  simp only [pow2_138, u1, pow2_139_q, f, pow2_139, pow2_139_mul_t]
  simp only [pow1_139]
  ring

theorem pow2_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_138 z * u1 z = pow2_139_q z * f z + pow2_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_139_mul_integer z


theorem pow2_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_138 z * u1 z = pow2_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_139_mul z


theorem pow2_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 139 = pow2_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow2_138_pow z hz]
  exact pow2_139_root z hz


theorem iterate2 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 2) = u2 z := by
  calc
    _ = (z ^ (139 ^ 1)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u1 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate1 z hz)
    _ = _ := pow2_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers02
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow3_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z + (139 : R) * pow3_2_mul_t z := by
  simp only [u2, pow3_2_q, f, pow3_2, pow3_2_mul_t]
  simp only [pow2_139]
  ring

theorem pow3_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_2_mul_integer z


theorem pow3_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z * u2 z = pow3_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_2_mul z


theorem pow3_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 2 = pow3_2 z := by
  calc
    _ = u2 z ^ 1 * u2 z ^ 1 := by ring
    _ = u2 z * u2 z := by simp only [pow_one]
    _ = _ := pow3_2_root z hz


theorem pow3_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z + (139 : R) * pow3_4_mul_t z := by
  simp only [pow3_2, pow3_4_q, f, pow3_4, pow3_4_mul_t]
  
  ring

theorem pow3_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_4_mul_integer z


theorem pow3_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_2 z * pow3_2 z = pow3_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_4_mul z


theorem pow3_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 4 = pow3_4 z := by
  calc
    _ = u2 z ^ 2 * u2 z ^ 2 := by ring
    _ = pow3_2 z * pow3_2 z := by rw [pow3_2_pow z hz]
    _ = _ := pow3_4_root z hz


theorem pow3_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_4 z * pow3_4 z = pow3_8_q z * f z + pow3_8 z + (139 : R) * pow3_8_mul_t z := by
  simp only [pow3_4, pow3_8_q, f, pow3_8, pow3_8_mul_t]
  
  ring

theorem pow3_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_4 z * pow3_4 z = pow3_8_q z * f z + pow3_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_8_mul_integer z


theorem pow3_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_4 z * pow3_4 z = pow3_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_8_mul z


theorem pow3_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 8 = pow3_8 z := by
  calc
    _ = u2 z ^ 4 * u2 z ^ 4 := by ring
    _ = pow3_4 z * pow3_4 z := by rw [pow3_4_pow z hz]
    _ = _ := pow3_8_root z hz


theorem pow3_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_8 z * pow3_8 z = pow3_16_q z * f z + pow3_16 z + (139 : R) * pow3_16_mul_t z := by
  simp only [pow3_8, pow3_16_q, f, pow3_16, pow3_16_mul_t]
  
  ring

theorem pow3_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_8 z * pow3_8 z = pow3_16_q z * f z + pow3_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_16_mul_integer z


theorem pow3_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_8 z * pow3_8 z = pow3_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_16_mul z


theorem pow3_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 16 = pow3_16 z := by
  calc
    _ = u2 z ^ 8 * u2 z ^ 8 := by ring
    _ = pow3_8 z * pow3_8 z := by rw [pow3_8_pow z hz]
    _ = _ := pow3_16_root z hz


theorem pow3_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_16 z * u2 z = pow3_17_q z * f z + pow3_17 z + (139 : R) * pow3_17_mul_t z := by
  simp only [pow3_16, u2, pow3_17_q, f, pow3_17, pow3_17_mul_t]
  simp only [pow2_139]
  ring

theorem pow3_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_16 z * u2 z = pow3_17_q z * f z + pow3_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_17_mul_integer z


theorem pow3_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_16 z * u2 z = pow3_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_17_mul z


theorem pow3_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 17 = pow3_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow3_16_pow z hz]
  exact pow3_17_root z hz


theorem pow3_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_17 z * pow3_17 z = pow3_34_q z * f z + pow3_34 z + (139 : R) * pow3_34_mul_t z := by
  simp only [pow3_17, pow3_34_q, f, pow3_34, pow3_34_mul_t]
  
  ring

theorem pow3_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_17 z * pow3_17 z = pow3_34_q z * f z + pow3_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_34_mul_integer z


theorem pow3_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_17 z * pow3_17 z = pow3_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_34_mul z


theorem pow3_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 34 = pow3_34 z := by
  calc
    _ = u2 z ^ 17 * u2 z ^ 17 := by ring
    _ = pow3_17 z * pow3_17 z := by rw [pow3_17_pow z hz]
    _ = _ := pow3_34_root z hz


theorem pow3_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_34 z * pow3_34 z = pow3_68_q z * f z + pow3_68 z + (139 : R) * pow3_68_mul_t z := by
  simp only [pow3_34, pow3_68_q, f, pow3_68, pow3_68_mul_t]
  
  ring

theorem pow3_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_34 z * pow3_34 z = pow3_68_q z * f z + pow3_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_68_mul_integer z


theorem pow3_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_34 z * pow3_34 z = pow3_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_68_mul z


theorem pow3_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 68 = pow3_68 z := by
  calc
    _ = u2 z ^ 34 * u2 z ^ 34 := by ring
    _ = pow3_34 z * pow3_34 z := by rw [pow3_34_pow z hz]
    _ = _ := pow3_68_root z hz


theorem pow3_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_68 z * u2 z = pow3_69_q z * f z + pow3_69 z + (139 : R) * pow3_69_mul_t z := by
  simp only [pow3_68, u2, pow3_69_q, f, pow3_69, pow3_69_mul_t]
  simp only [pow2_139]
  ring

theorem pow3_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_68 z * u2 z = pow3_69_q z * f z + pow3_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_69_mul_integer z


theorem pow3_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_68 z * u2 z = pow3_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_69_mul z


theorem pow3_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 69 = pow3_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow3_68_pow z hz]
  exact pow3_69_root z hz


theorem pow3_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_69 z * pow3_69 z = pow3_138_q z * f z + pow3_138 z + (139 : R) * pow3_138_mul_t z := by
  simp only [pow3_69, pow3_138_q, f, pow3_138, pow3_138_mul_t]
  
  ring

theorem pow3_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_69 z * pow3_69 z = pow3_138_q z * f z + pow3_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_138_mul_integer z


theorem pow3_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_69 z * pow3_69 z = pow3_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_138_mul z


theorem pow3_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 138 = pow3_138 z := by
  calc
    _ = u2 z ^ 69 * u2 z ^ 69 := by ring
    _ = pow3_69 z * pow3_69 z := by rw [pow3_69_pow z hz]
    _ = _ := pow3_138_root z hz


theorem pow3_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_138 z * u2 z = pow3_139_q z * f z + pow3_139 z + (139 : R) * pow3_139_mul_t z := by
  simp only [pow3_138, u2, pow3_139_q, f, pow3_139, pow3_139_mul_t]
  simp only [pow2_139]
  ring

theorem pow3_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_138 z * u2 z = pow3_139_q z * f z + pow3_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_139_mul_integer z


theorem pow3_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_138 z * u2 z = pow3_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_139_mul z


theorem pow3_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 139 = pow3_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow3_138_pow z hz]
  exact pow3_139_root z hz


theorem iterate3 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 3) = u3 z := by
  calc
    _ = (z ^ (139 ^ 2)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u2 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate2 z hz)
    _ = _ := pow3_139_pow z hz


theorem pow4_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z + (139 : R) * pow4_2_mul_t z := by
  simp only [u3, pow4_2_q, f, pow4_2, pow4_2_mul_t]
  simp only [pow3_139]
  ring

theorem pow4_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_2_mul_integer z


theorem pow4_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z * u3 z = pow4_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_2_mul z


theorem pow4_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 2 = pow4_2 z := by
  calc
    _ = u3 z ^ 1 * u3 z ^ 1 := by ring
    _ = u3 z * u3 z := by simp only [pow_one]
    _ = _ := pow4_2_root z hz


theorem pow4_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z + (139 : R) * pow4_4_mul_t z := by
  simp only [pow4_2, pow4_4_q, f, pow4_4, pow4_4_mul_t]
  
  ring

theorem pow4_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_4_mul_integer z


theorem pow4_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_2 z * pow4_2 z = pow4_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_4_mul z


theorem pow4_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 4 = pow4_4 z := by
  calc
    _ = u3 z ^ 2 * u3 z ^ 2 := by ring
    _ = pow4_2 z * pow4_2 z := by rw [pow4_2_pow z hz]
    _ = _ := pow4_4_root z hz


theorem pow4_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_4 z * pow4_4 z = pow4_8_q z * f z + pow4_8 z + (139 : R) * pow4_8_mul_t z := by
  simp only [pow4_4, pow4_8_q, f, pow4_8, pow4_8_mul_t]
  
  ring

theorem pow4_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_4 z * pow4_4 z = pow4_8_q z * f z + pow4_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_8_mul_integer z


theorem pow4_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_4 z * pow4_4 z = pow4_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_8_mul z


theorem pow4_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 8 = pow4_8 z := by
  calc
    _ = u3 z ^ 4 * u3 z ^ 4 := by ring
    _ = pow4_4 z * pow4_4 z := by rw [pow4_4_pow z hz]
    _ = _ := pow4_8_root z hz


theorem pow4_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_8 z * pow4_8 z = pow4_16_q z * f z + pow4_16 z + (139 : R) * pow4_16_mul_t z := by
  simp only [pow4_8, pow4_16_q, f, pow4_16, pow4_16_mul_t]
  
  ring

theorem pow4_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_8 z * pow4_8 z = pow4_16_q z * f z + pow4_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_16_mul_integer z


theorem pow4_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_8 z * pow4_8 z = pow4_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_16_mul z


theorem pow4_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 16 = pow4_16 z := by
  calc
    _ = u3 z ^ 8 * u3 z ^ 8 := by ring
    _ = pow4_8 z * pow4_8 z := by rw [pow4_8_pow z hz]
    _ = _ := pow4_16_root z hz


theorem pow4_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_16 z * u3 z = pow4_17_q z * f z + pow4_17 z + (139 : R) * pow4_17_mul_t z := by
  simp only [pow4_16, u3, pow4_17_q, f, pow4_17, pow4_17_mul_t]
  simp only [pow3_139]
  ring

theorem pow4_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_16 z * u3 z = pow4_17_q z * f z + pow4_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_17_mul_integer z


theorem pow4_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_16 z * u3 z = pow4_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_17_mul z


theorem pow4_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 17 = pow4_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow4_16_pow z hz]
  exact pow4_17_root z hz


theorem pow4_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_17 z * pow4_17 z = pow4_34_q z * f z + pow4_34 z + (139 : R) * pow4_34_mul_t z := by
  simp only [pow4_17, pow4_34_q, f, pow4_34, pow4_34_mul_t]
  
  ring

theorem pow4_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_17 z * pow4_17 z = pow4_34_q z * f z + pow4_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_34_mul_integer z


theorem pow4_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_17 z * pow4_17 z = pow4_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_34_mul z


theorem pow4_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 34 = pow4_34 z := by
  calc
    _ = u3 z ^ 17 * u3 z ^ 17 := by ring
    _ = pow4_17 z * pow4_17 z := by rw [pow4_17_pow z hz]
    _ = _ := pow4_34_root z hz


theorem pow4_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_34 z * pow4_34 z = pow4_68_q z * f z + pow4_68 z + (139 : R) * pow4_68_mul_t z := by
  simp only [pow4_34, pow4_68_q, f, pow4_68, pow4_68_mul_t]
  
  ring

theorem pow4_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_34 z * pow4_34 z = pow4_68_q z * f z + pow4_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_68_mul_integer z


theorem pow4_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_34 z * pow4_34 z = pow4_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_68_mul z


theorem pow4_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 68 = pow4_68 z := by
  calc
    _ = u3 z ^ 34 * u3 z ^ 34 := by ring
    _ = pow4_34 z * pow4_34 z := by rw [pow4_34_pow z hz]
    _ = _ := pow4_68_root z hz


theorem pow4_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_68 z * u3 z = pow4_69_q z * f z + pow4_69 z + (139 : R) * pow4_69_mul_t z := by
  simp only [pow4_68, u3, pow4_69_q, f, pow4_69, pow4_69_mul_t]
  simp only [pow3_139]
  ring

theorem pow4_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_68 z * u3 z = pow4_69_q z * f z + pow4_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_69_mul_integer z


theorem pow4_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_68 z * u3 z = pow4_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_69_mul z


theorem pow4_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 69 = pow4_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow4_68_pow z hz]
  exact pow4_69_root z hz


theorem pow4_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_69 z * pow4_69 z = pow4_138_q z * f z + pow4_138 z + (139 : R) * pow4_138_mul_t z := by
  simp only [pow4_69, pow4_138_q, f, pow4_138, pow4_138_mul_t]
  
  ring

theorem pow4_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_69 z * pow4_69 z = pow4_138_q z * f z + pow4_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_138_mul_integer z


theorem pow4_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_69 z * pow4_69 z = pow4_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_138_mul z


theorem pow4_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 138 = pow4_138 z := by
  calc
    _ = u3 z ^ 69 * u3 z ^ 69 := by ring
    _ = pow4_69 z * pow4_69 z := by rw [pow4_69_pow z hz]
    _ = _ := pow4_138_root z hz


theorem pow4_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_138 z * u3 z = pow4_139_q z * f z + pow4_139 z + (139 : R) * pow4_139_mul_t z := by
  simp only [pow4_138, u3, pow4_139_q, f, pow4_139, pow4_139_mul_t]
  simp only [pow3_139]
  ring

theorem pow4_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_138 z * u3 z = pow4_139_q z * f z + pow4_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_139_mul_integer z


theorem pow4_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_138 z * u3 z = pow4_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_139_mul z


theorem pow4_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 139 = pow4_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow4_138_pow z hz]
  exact pow4_139_root z hz


theorem iterate4 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 4) = u4 z := by
  calc
    _ = (z ^ (139 ^ 3)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u3 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate3 z hz)
    _ = _ := pow4_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers03
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow5_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z + (139 : R) * pow5_2_mul_t z := by
  simp only [u4, pow5_2_q, f, pow5_2, pow5_2_mul_t]
  simp only [pow4_139]
  ring

theorem pow5_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_2_mul_integer z


theorem pow5_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z * u4 z = pow5_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_2_mul z


theorem pow5_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 2 = pow5_2 z := by
  calc
    _ = u4 z ^ 1 * u4 z ^ 1 := by ring
    _ = u4 z * u4 z := by simp only [pow_one]
    _ = _ := pow5_2_root z hz


theorem pow5_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z + (139 : R) * pow5_4_mul_t z := by
  simp only [pow5_2, pow5_4_q, f, pow5_4, pow5_4_mul_t]
  
  ring

theorem pow5_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_4_mul_integer z


theorem pow5_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_2 z * pow5_2 z = pow5_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_4_mul z


theorem pow5_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 4 = pow5_4 z := by
  calc
    _ = u4 z ^ 2 * u4 z ^ 2 := by ring
    _ = pow5_2 z * pow5_2 z := by rw [pow5_2_pow z hz]
    _ = _ := pow5_4_root z hz


theorem pow5_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_4 z * pow5_4 z = pow5_8_q z * f z + pow5_8 z + (139 : R) * pow5_8_mul_t z := by
  simp only [pow5_4, pow5_8_q, f, pow5_8, pow5_8_mul_t]
  
  ring

theorem pow5_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_4 z * pow5_4 z = pow5_8_q z * f z + pow5_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_8_mul_integer z


theorem pow5_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_4 z * pow5_4 z = pow5_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_8_mul z


theorem pow5_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 8 = pow5_8 z := by
  calc
    _ = u4 z ^ 4 * u4 z ^ 4 := by ring
    _ = pow5_4 z * pow5_4 z := by rw [pow5_4_pow z hz]
    _ = _ := pow5_8_root z hz


theorem pow5_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_8 z * pow5_8 z = pow5_16_q z * f z + pow5_16 z + (139 : R) * pow5_16_mul_t z := by
  simp only [pow5_8, pow5_16_q, f, pow5_16, pow5_16_mul_t]
  
  ring

theorem pow5_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_8 z * pow5_8 z = pow5_16_q z * f z + pow5_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_16_mul_integer z


theorem pow5_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_8 z * pow5_8 z = pow5_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_16_mul z


theorem pow5_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 16 = pow5_16 z := by
  calc
    _ = u4 z ^ 8 * u4 z ^ 8 := by ring
    _ = pow5_8 z * pow5_8 z := by rw [pow5_8_pow z hz]
    _ = _ := pow5_16_root z hz


theorem pow5_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_16 z * u4 z = pow5_17_q z * f z + pow5_17 z + (139 : R) * pow5_17_mul_t z := by
  simp only [pow5_16, u4, pow5_17_q, f, pow5_17, pow5_17_mul_t]
  simp only [pow4_139]
  ring

theorem pow5_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_16 z * u4 z = pow5_17_q z * f z + pow5_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_17_mul_integer z


theorem pow5_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_16 z * u4 z = pow5_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_17_mul z


theorem pow5_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 17 = pow5_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow5_16_pow z hz]
  exact pow5_17_root z hz


theorem pow5_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_17 z * pow5_17 z = pow5_34_q z * f z + pow5_34 z + (139 : R) * pow5_34_mul_t z := by
  simp only [pow5_17, pow5_34_q, f, pow5_34, pow5_34_mul_t]
  
  ring

theorem pow5_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_17 z * pow5_17 z = pow5_34_q z * f z + pow5_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_34_mul_integer z


theorem pow5_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_17 z * pow5_17 z = pow5_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_34_mul z


theorem pow5_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 34 = pow5_34 z := by
  calc
    _ = u4 z ^ 17 * u4 z ^ 17 := by ring
    _ = pow5_17 z * pow5_17 z := by rw [pow5_17_pow z hz]
    _ = _ := pow5_34_root z hz


theorem pow5_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_34 z * pow5_34 z = pow5_68_q z * f z + pow5_68 z + (139 : R) * pow5_68_mul_t z := by
  simp only [pow5_34, pow5_68_q, f, pow5_68, pow5_68_mul_t]
  
  ring

theorem pow5_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_34 z * pow5_34 z = pow5_68_q z * f z + pow5_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_68_mul_integer z


theorem pow5_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_34 z * pow5_34 z = pow5_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_68_mul z


theorem pow5_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 68 = pow5_68 z := by
  calc
    _ = u4 z ^ 34 * u4 z ^ 34 := by ring
    _ = pow5_34 z * pow5_34 z := by rw [pow5_34_pow z hz]
    _ = _ := pow5_68_root z hz


theorem pow5_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_68 z * u4 z = pow5_69_q z * f z + pow5_69 z + (139 : R) * pow5_69_mul_t z := by
  simp only [pow5_68, u4, pow5_69_q, f, pow5_69, pow5_69_mul_t]
  simp only [pow4_139]
  ring

theorem pow5_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_68 z * u4 z = pow5_69_q z * f z + pow5_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_69_mul_integer z


theorem pow5_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_68 z * u4 z = pow5_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_69_mul z


theorem pow5_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 69 = pow5_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow5_68_pow z hz]
  exact pow5_69_root z hz


theorem pow5_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_69 z * pow5_69 z = pow5_138_q z * f z + pow5_138 z + (139 : R) * pow5_138_mul_t z := by
  simp only [pow5_69, pow5_138_q, f, pow5_138, pow5_138_mul_t]
  
  ring

theorem pow5_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_69 z * pow5_69 z = pow5_138_q z * f z + pow5_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_138_mul_integer z


theorem pow5_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_69 z * pow5_69 z = pow5_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_138_mul z


theorem pow5_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 138 = pow5_138 z := by
  calc
    _ = u4 z ^ 69 * u4 z ^ 69 := by ring
    _ = pow5_69 z * pow5_69 z := by rw [pow5_69_pow z hz]
    _ = _ := pow5_138_root z hz


theorem pow5_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_138 z * u4 z = pow5_139_q z * f z + pow5_139 z + (139 : R) * pow5_139_mul_t z := by
  simp only [pow5_138, u4, pow5_139_q, f, pow5_139, pow5_139_mul_t]
  simp only [pow4_139]
  ring

theorem pow5_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_138 z * u4 z = pow5_139_q z * f z + pow5_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_139_mul_integer z


theorem pow5_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_138 z * u4 z = pow5_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_139_mul z


theorem pow5_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 139 = pow5_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow5_138_pow z hz]
  exact pow5_139_root z hz


theorem iterate5 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 5) = u5 z := by
  calc
    _ = (z ^ (139 ^ 4)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u4 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate4 z hz)
    _ = _ := pow5_139_pow z hz


theorem pow6_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z + (139 : R) * pow6_2_mul_t z := by
  simp only [u5, pow6_2_q, f, pow6_2, pow6_2_mul_t]
  simp only [pow5_139]
  ring

theorem pow6_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_2_mul_integer z


theorem pow6_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z * u5 z = pow6_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_2_mul z


theorem pow6_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 2 = pow6_2 z := by
  calc
    _ = u5 z ^ 1 * u5 z ^ 1 := by ring
    _ = u5 z * u5 z := by simp only [pow_one]
    _ = _ := pow6_2_root z hz


theorem pow6_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z + (139 : R) * pow6_4_mul_t z := by
  simp only [pow6_2, pow6_4_q, f, pow6_4, pow6_4_mul_t]
  
  ring

theorem pow6_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_4_mul_integer z


theorem pow6_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_2 z * pow6_2 z = pow6_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_4_mul z


theorem pow6_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 4 = pow6_4 z := by
  calc
    _ = u5 z ^ 2 * u5 z ^ 2 := by ring
    _ = pow6_2 z * pow6_2 z := by rw [pow6_2_pow z hz]
    _ = _ := pow6_4_root z hz


theorem pow6_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_4 z * pow6_4 z = pow6_8_q z * f z + pow6_8 z + (139 : R) * pow6_8_mul_t z := by
  simp only [pow6_4, pow6_8_q, f, pow6_8, pow6_8_mul_t]
  
  ring

theorem pow6_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_4 z * pow6_4 z = pow6_8_q z * f z + pow6_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_8_mul_integer z


theorem pow6_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_4 z * pow6_4 z = pow6_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_8_mul z


theorem pow6_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 8 = pow6_8 z := by
  calc
    _ = u5 z ^ 4 * u5 z ^ 4 := by ring
    _ = pow6_4 z * pow6_4 z := by rw [pow6_4_pow z hz]
    _ = _ := pow6_8_root z hz


theorem pow6_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_8 z * pow6_8 z = pow6_16_q z * f z + pow6_16 z + (139 : R) * pow6_16_mul_t z := by
  simp only [pow6_8, pow6_16_q, f, pow6_16, pow6_16_mul_t]
  
  ring

theorem pow6_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_8 z * pow6_8 z = pow6_16_q z * f z + pow6_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_16_mul_integer z


theorem pow6_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_8 z * pow6_8 z = pow6_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_16_mul z


theorem pow6_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 16 = pow6_16 z := by
  calc
    _ = u5 z ^ 8 * u5 z ^ 8 := by ring
    _ = pow6_8 z * pow6_8 z := by rw [pow6_8_pow z hz]
    _ = _ := pow6_16_root z hz


theorem pow6_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_16 z * u5 z = pow6_17_q z * f z + pow6_17 z + (139 : R) * pow6_17_mul_t z := by
  simp only [pow6_16, u5, pow6_17_q, f, pow6_17, pow6_17_mul_t]
  simp only [pow5_139]
  ring

theorem pow6_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_16 z * u5 z = pow6_17_q z * f z + pow6_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_17_mul_integer z


theorem pow6_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_16 z * u5 z = pow6_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_17_mul z


theorem pow6_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 17 = pow6_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow6_16_pow z hz]
  exact pow6_17_root z hz


theorem pow6_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_17 z * pow6_17 z = pow6_34_q z * f z + pow6_34 z + (139 : R) * pow6_34_mul_t z := by
  simp only [pow6_17, pow6_34_q, f, pow6_34, pow6_34_mul_t]
  
  ring

theorem pow6_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_17 z * pow6_17 z = pow6_34_q z * f z + pow6_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_34_mul_integer z


theorem pow6_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_17 z * pow6_17 z = pow6_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_34_mul z


theorem pow6_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 34 = pow6_34 z := by
  calc
    _ = u5 z ^ 17 * u5 z ^ 17 := by ring
    _ = pow6_17 z * pow6_17 z := by rw [pow6_17_pow z hz]
    _ = _ := pow6_34_root z hz


theorem pow6_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_34 z * pow6_34 z = pow6_68_q z * f z + pow6_68 z + (139 : R) * pow6_68_mul_t z := by
  simp only [pow6_34, pow6_68_q, f, pow6_68, pow6_68_mul_t]
  
  ring

theorem pow6_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_34 z * pow6_34 z = pow6_68_q z * f z + pow6_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_68_mul_integer z


theorem pow6_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_34 z * pow6_34 z = pow6_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_68_mul z


theorem pow6_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 68 = pow6_68 z := by
  calc
    _ = u5 z ^ 34 * u5 z ^ 34 := by ring
    _ = pow6_34 z * pow6_34 z := by rw [pow6_34_pow z hz]
    _ = _ := pow6_68_root z hz


theorem pow6_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_68 z * u5 z = pow6_69_q z * f z + pow6_69 z + (139 : R) * pow6_69_mul_t z := by
  simp only [pow6_68, u5, pow6_69_q, f, pow6_69, pow6_69_mul_t]
  simp only [pow5_139]
  ring

theorem pow6_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_68 z * u5 z = pow6_69_q z * f z + pow6_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_69_mul_integer z


theorem pow6_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_68 z * u5 z = pow6_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_69_mul z


theorem pow6_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 69 = pow6_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow6_68_pow z hz]
  exact pow6_69_root z hz


theorem pow6_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_69 z * pow6_69 z = pow6_138_q z * f z + pow6_138 z + (139 : R) * pow6_138_mul_t z := by
  simp only [pow6_69, pow6_138_q, f, pow6_138, pow6_138_mul_t]
  
  ring

theorem pow6_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_69 z * pow6_69 z = pow6_138_q z * f z + pow6_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_138_mul_integer z


theorem pow6_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_69 z * pow6_69 z = pow6_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_138_mul z


theorem pow6_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 138 = pow6_138 z := by
  calc
    _ = u5 z ^ 69 * u5 z ^ 69 := by ring
    _ = pow6_69 z * pow6_69 z := by rw [pow6_69_pow z hz]
    _ = _ := pow6_138_root z hz


theorem pow6_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_138 z * u5 z = pow6_139_q z * f z + pow6_139 z + (139 : R) * pow6_139_mul_t z := by
  simp only [pow6_138, u5, pow6_139_q, f, pow6_139, pow6_139_mul_t]
  simp only [pow5_139]
  ring

theorem pow6_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_138 z * u5 z = pow6_139_q z * f z + pow6_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_139_mul_integer z


theorem pow6_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_138 z * u5 z = pow6_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_139_mul z


theorem pow6_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 139 = pow6_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow6_138_pow z hz]
  exact pow6_139_root z hz


theorem iterate6 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 6) = u6 z := by
  calc
    _ = (z ^ (139 ^ 5)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u5 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate5 z hz)
    _ = _ := pow6_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers04
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers05
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers06
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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


theorem iterate12 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 12) = u12 z := by
  calc
    _ = (z ^ (139 ^ 11)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u11 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate11 z hz)
    _ = _ := pow12_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers07
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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


theorem iterate14_s2_oai {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 14) = u14 z := by
  calc
    _ = (z ^ (139 ^ 13)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u13 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate13 z hz)
    _ = _ := pow14_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Mod139.iterate14_s2_oai.{u_1} := @OAI.DimensionTen.Mod139.iterate14_s2_oai.{u_1}
