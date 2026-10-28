-- Prove2me | solution 1 for OAI.DimensionTen.Mod139.iterate6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:20:37.080515+00:00
-- url     : https://prove2.me/submissions/a57393fe-a884-421e-b9f7-c77af35ec0e3

import Mathlib
import Definitions.Def_OAIQ033D009
import Definitions.Def_OAIQ033D013

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Model
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
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
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
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
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers02
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
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
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers03
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
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


theorem iterate6_oai {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 6) = u6 z := by
  calc
    _ = (z ^ (139 ^ 5)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u5 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate5 z hz)
    _ = _ := pow6_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Mod139.iterate6_oai.{u_1} := @OAI.DimensionTen.Mod139.iterate6_oai.{u_1}
