-- Prove2me | solution 1 for OAI.DimensionTen.fixed_mod131_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:13:59.964892+00:00
-- url     : https://prove2.me/submissions/44e212e7-3d1f-4934-889b-83fe6ff1c810

import Mathlib
import Definitions.Def_OAIQ057D009
import Theorems.Thm_OAI_DimensionTen_Mod131_iterate13_s2

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_FrobeniusRoots
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma iterate_pow_perm {ι R : Type*} [Monoid R] (σ : Equiv.Perm ι) (r : ι → R)
    (p : ℕ) (h : ∀ i, r (σ i) = r i ^ p) (n : ℕ) :
    ∀ i, r ((σ ^ n) i) = r i ^ (p ^ n) := by
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    rw [pow_succ', Equiv.Perm.mul_apply, h, ih, ← pow_mul, pow_succ]

end DimensionTen

end
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

theorem pow14_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z + (131 : R) * pow14_2_mul_t z := by
  simp only [u13, pow14_2_q, f, pow14_2, pow14_2_mul_t]
  simp only [pow13_131]
  ring

theorem pow14_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_2_mul_integer z


theorem pow14_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z * u13 z = pow14_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_2_mul z


theorem pow14_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 2 = pow14_2 z := by
  calc
    _ = u13 z ^ 1 * u13 z ^ 1 := by ring
    _ = u13 z * u13 z := by simp only [pow_one]
    _ = _ := pow14_2_root z hz


theorem pow14_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z + (131 : R) * pow14_4_mul_t z := by
  simp only [pow14_2, pow14_4_q, f, pow14_4, pow14_4_mul_t]
  
  ring

theorem pow14_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_4_mul_integer z


theorem pow14_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_2 z * pow14_2 z = pow14_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_4_mul z


theorem pow14_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 4 = pow14_4 z := by
  calc
    _ = u13 z ^ 2 * u13 z ^ 2 := by ring
    _ = pow14_2 z * pow14_2 z := by rw [pow14_2_pow z hz]
    _ = _ := pow14_4_root z hz


theorem pow14_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_4 z * pow14_4 z = pow14_8_q z * f z + pow14_8 z + (131 : R) * pow14_8_mul_t z := by
  simp only [pow14_4, pow14_8_q, f, pow14_8, pow14_8_mul_t]
  
  ring

theorem pow14_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_4 z * pow14_4 z = pow14_8_q z * f z + pow14_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_8_mul_integer z


theorem pow14_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_4 z * pow14_4 z = pow14_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_8_mul z


theorem pow14_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 8 = pow14_8 z := by
  calc
    _ = u13 z ^ 4 * u13 z ^ 4 := by ring
    _ = pow14_4 z * pow14_4 z := by rw [pow14_4_pow z hz]
    _ = _ := pow14_8_root z hz


theorem pow14_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_8 z * pow14_8 z = pow14_16_q z * f z + pow14_16 z + (131 : R) * pow14_16_mul_t z := by
  simp only [pow14_8, pow14_16_q, f, pow14_16, pow14_16_mul_t]
  
  ring

theorem pow14_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_8 z * pow14_8 z = pow14_16_q z * f z + pow14_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_16_mul_integer z


theorem pow14_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_8 z * pow14_8 z = pow14_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_16_mul z


theorem pow14_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 16 = pow14_16 z := by
  calc
    _ = u13 z ^ 8 * u13 z ^ 8 := by ring
    _ = pow14_8 z * pow14_8 z := by rw [pow14_8_pow z hz]
    _ = _ := pow14_16_root z hz


theorem pow14_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_16 z * pow14_16 z = pow14_32_q z * f z + pow14_32 z + (131 : R) * pow14_32_mul_t z := by
  simp only [pow14_16, pow14_32_q, f, pow14_32, pow14_32_mul_t]
  
  ring

theorem pow14_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_16 z * pow14_16 z = pow14_32_q z * f z + pow14_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_32_mul_integer z


theorem pow14_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_16 z * pow14_16 z = pow14_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_32_mul z


theorem pow14_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 32 = pow14_32 z := by
  calc
    _ = u13 z ^ 16 * u13 z ^ 16 := by ring
    _ = pow14_16 z * pow14_16 z := by rw [pow14_16_pow z hz]
    _ = _ := pow14_32_root z hz


theorem pow14_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_32 z * pow14_32 z = pow14_64_q z * f z + pow14_64 z + (131 : R) * pow14_64_mul_t z := by
  simp only [pow14_32, pow14_64_q, f, pow14_64, pow14_64_mul_t]
  
  ring

theorem pow14_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_32 z * pow14_32 z = pow14_64_q z * f z + pow14_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_64_mul_integer z


theorem pow14_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_32 z * pow14_32 z = pow14_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_64_mul z


theorem pow14_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 64 = pow14_64 z := by
  calc
    _ = u13 z ^ 32 * u13 z ^ 32 := by ring
    _ = pow14_32 z * pow14_32 z := by rw [pow14_32_pow z hz]
    _ = _ := pow14_64_root z hz


theorem pow14_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_64 z * u13 z = pow14_65_q z * f z + pow14_65 z + (131 : R) * pow14_65_mul_t z := by
  simp only [pow14_64, u13, pow14_65_q, f, pow14_65, pow14_65_mul_t]
  simp only [pow13_131]
  ring

theorem pow14_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_64 z * u13 z = pow14_65_q z * f z + pow14_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_65_mul_integer z


theorem pow14_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_64 z * u13 z = pow14_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_65_mul z


theorem pow14_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 65 = pow14_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow14_64_pow z hz]
  exact pow14_65_root z hz


theorem pow14_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_65 z * pow14_65 z = pow14_130_q z * f z + pow14_130 z + (131 : R) * pow14_130_mul_t z := by
  simp only [pow14_65, pow14_130_q, f, pow14_130, pow14_130_mul_t]
  
  ring

theorem pow14_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_65 z * pow14_65 z = pow14_130_q z * f z + pow14_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_130_mul_integer z


theorem pow14_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_65 z * pow14_65 z = pow14_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_130_mul z


theorem pow14_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 130 = pow14_130 z := by
  calc
    _ = u13 z ^ 65 * u13 z ^ 65 := by ring
    _ = pow14_65 z * pow14_65 z := by rw [pow14_65_pow z hz]
    _ = _ := pow14_130_root z hz


theorem pow14_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_130 z * u13 z = pow14_131_q z * f z + pow14_131 z + (131 : R) * pow14_131_mul_t z := by
  simp only [pow14_130, u13, pow14_131_q, f, pow14_131, pow14_131_mul_t]
  simp only [pow13_131]
  ring

theorem pow14_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_130 z * u13 z = pow14_131_q z * f z + pow14_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_131_mul_integer z


theorem pow14_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_130 z * u13 z = pow14_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_131_mul z


theorem pow14_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 131 = pow14_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow14_130_pow z hz]
  exact pow14_131_root z hz


theorem iterate14 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 14) = u14 z := by
  calc
    _ = (z ^ (131 ^ 13)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u13 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate13_s2 z hz)
    _ = _ := pow14_131_pow z hz

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers08
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow15_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z + (131 : R) * pow15_2_mul_t z := by
  simp only [u14, pow15_2_q, f, pow15_2, pow15_2_mul_t]
  simp only [pow14_131]
  ring

theorem pow15_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_2_mul_integer z


theorem pow15_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z * u14 z = pow15_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_2_mul z


theorem pow15_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 2 = pow15_2 z := by
  calc
    _ = u14 z ^ 1 * u14 z ^ 1 := by ring
    _ = u14 z * u14 z := by simp only [pow_one]
    _ = _ := pow15_2_root z hz


theorem pow15_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z + (131 : R) * pow15_4_mul_t z := by
  simp only [pow15_2, pow15_4_q, f, pow15_4, pow15_4_mul_t]
  
  ring

theorem pow15_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_4_mul_integer z


theorem pow15_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_2 z * pow15_2 z = pow15_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_4_mul z


theorem pow15_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 4 = pow15_4 z := by
  calc
    _ = u14 z ^ 2 * u14 z ^ 2 := by ring
    _ = pow15_2 z * pow15_2 z := by rw [pow15_2_pow z hz]
    _ = _ := pow15_4_root z hz


theorem pow15_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_4 z * pow15_4 z = pow15_8_q z * f z + pow15_8 z + (131 : R) * pow15_8_mul_t z := by
  simp only [pow15_4, pow15_8_q, f, pow15_8, pow15_8_mul_t]
  
  ring

theorem pow15_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_4 z * pow15_4 z = pow15_8_q z * f z + pow15_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_8_mul_integer z


theorem pow15_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_4 z * pow15_4 z = pow15_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_8_mul z


theorem pow15_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 8 = pow15_8 z := by
  calc
    _ = u14 z ^ 4 * u14 z ^ 4 := by ring
    _ = pow15_4 z * pow15_4 z := by rw [pow15_4_pow z hz]
    _ = _ := pow15_8_root z hz


theorem pow15_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_8 z * pow15_8 z = pow15_16_q z * f z + pow15_16 z + (131 : R) * pow15_16_mul_t z := by
  simp only [pow15_8, pow15_16_q, f, pow15_16, pow15_16_mul_t]
  
  ring

theorem pow15_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_8 z * pow15_8 z = pow15_16_q z * f z + pow15_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_16_mul_integer z


theorem pow15_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_8 z * pow15_8 z = pow15_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_16_mul z


theorem pow15_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 16 = pow15_16 z := by
  calc
    _ = u14 z ^ 8 * u14 z ^ 8 := by ring
    _ = pow15_8 z * pow15_8 z := by rw [pow15_8_pow z hz]
    _ = _ := pow15_16_root z hz


theorem pow15_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_16 z * pow15_16 z = pow15_32_q z * f z + pow15_32 z + (131 : R) * pow15_32_mul_t z := by
  simp only [pow15_16, pow15_32_q, f, pow15_32, pow15_32_mul_t]
  
  ring

theorem pow15_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_16 z * pow15_16 z = pow15_32_q z * f z + pow15_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_32_mul_integer z


theorem pow15_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_16 z * pow15_16 z = pow15_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_32_mul z


theorem pow15_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 32 = pow15_32 z := by
  calc
    _ = u14 z ^ 16 * u14 z ^ 16 := by ring
    _ = pow15_16 z * pow15_16 z := by rw [pow15_16_pow z hz]
    _ = _ := pow15_32_root z hz


theorem pow15_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_32 z * pow15_32 z = pow15_64_q z * f z + pow15_64 z + (131 : R) * pow15_64_mul_t z := by
  simp only [pow15_32, pow15_64_q, f, pow15_64, pow15_64_mul_t]
  
  ring

theorem pow15_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_32 z * pow15_32 z = pow15_64_q z * f z + pow15_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_64_mul_integer z


theorem pow15_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_32 z * pow15_32 z = pow15_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_64_mul z


theorem pow15_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 64 = pow15_64 z := by
  calc
    _ = u14 z ^ 32 * u14 z ^ 32 := by ring
    _ = pow15_32 z * pow15_32 z := by rw [pow15_32_pow z hz]
    _ = _ := pow15_64_root z hz


theorem pow15_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_64 z * u14 z = pow15_65_q z * f z + pow15_65 z + (131 : R) * pow15_65_mul_t z := by
  simp only [pow15_64, u14, pow15_65_q, f, pow15_65, pow15_65_mul_t]
  simp only [pow14_131]
  ring

theorem pow15_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_64 z * u14 z = pow15_65_q z * f z + pow15_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_65_mul_integer z


theorem pow15_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_64 z * u14 z = pow15_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_65_mul z


theorem pow15_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 65 = pow15_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow15_64_pow z hz]
  exact pow15_65_root z hz


theorem pow15_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_65 z * pow15_65 z = pow15_130_q z * f z + pow15_130 z + (131 : R) * pow15_130_mul_t z := by
  simp only [pow15_65, pow15_130_q, f, pow15_130, pow15_130_mul_t]
  
  ring

theorem pow15_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_65 z * pow15_65 z = pow15_130_q z * f z + pow15_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_130_mul_integer z


theorem pow15_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_65 z * pow15_65 z = pow15_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_130_mul z


theorem pow15_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 130 = pow15_130 z := by
  calc
    _ = u14 z ^ 65 * u14 z ^ 65 := by ring
    _ = pow15_65 z * pow15_65 z := by rw [pow15_65_pow z hz]
    _ = _ := pow15_130_root z hz


theorem pow15_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_130 z * u14 z = pow15_131_q z * f z + pow15_131 z + (131 : R) * pow15_131_mul_t z := by
  simp only [pow15_130, u14, pow15_131_q, f, pow15_131, pow15_131_mul_t]
  simp only [pow14_131]
  ring

theorem pow15_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_130 z * u14 z = pow15_131_q z * f z + pow15_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_131_mul_integer z


theorem pow15_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_130 z * u14 z = pow15_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_131_mul z


theorem pow15_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 131 = pow15_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow15_130_pow z hz]
  exact pow15_131_root z hz


theorem iterate15 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 15) = u15 z := by
  calc
    _ = (z ^ (131 ^ 14)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u14 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate14 z hz)
    _ = _ := pow15_131_pow z hz


theorem pow16_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z + (131 : R) * pow16_2_mul_t z := by
  simp only [u15, pow16_2_q, f, pow16_2, pow16_2_mul_t]
  simp only [pow15_131]
  ring

theorem pow16_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_2_mul_integer z


theorem pow16_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z * u15 z = pow16_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_2_mul z


theorem pow16_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 2 = pow16_2 z := by
  calc
    _ = u15 z ^ 1 * u15 z ^ 1 := by ring
    _ = u15 z * u15 z := by simp only [pow_one]
    _ = _ := pow16_2_root z hz


theorem pow16_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z + (131 : R) * pow16_4_mul_t z := by
  simp only [pow16_2, pow16_4_q, f, pow16_4, pow16_4_mul_t]
  
  ring

theorem pow16_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_4_mul_integer z


theorem pow16_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_2 z * pow16_2 z = pow16_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_4_mul z


theorem pow16_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 4 = pow16_4 z := by
  calc
    _ = u15 z ^ 2 * u15 z ^ 2 := by ring
    _ = pow16_2 z * pow16_2 z := by rw [pow16_2_pow z hz]
    _ = _ := pow16_4_root z hz


theorem pow16_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_4 z * pow16_4 z = pow16_8_q z * f z + pow16_8 z + (131 : R) * pow16_8_mul_t z := by
  simp only [pow16_4, pow16_8_q, f, pow16_8, pow16_8_mul_t]
  
  ring

theorem pow16_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_4 z * pow16_4 z = pow16_8_q z * f z + pow16_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_8_mul_integer z


theorem pow16_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_4 z * pow16_4 z = pow16_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_8_mul z


theorem pow16_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 8 = pow16_8 z := by
  calc
    _ = u15 z ^ 4 * u15 z ^ 4 := by ring
    _ = pow16_4 z * pow16_4 z := by rw [pow16_4_pow z hz]
    _ = _ := pow16_8_root z hz


theorem pow16_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_8 z * pow16_8 z = pow16_16_q z * f z + pow16_16 z + (131 : R) * pow16_16_mul_t z := by
  simp only [pow16_8, pow16_16_q, f, pow16_16, pow16_16_mul_t]
  
  ring

theorem pow16_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_8 z * pow16_8 z = pow16_16_q z * f z + pow16_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_16_mul_integer z


theorem pow16_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_8 z * pow16_8 z = pow16_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_16_mul z


theorem pow16_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 16 = pow16_16 z := by
  calc
    _ = u15 z ^ 8 * u15 z ^ 8 := by ring
    _ = pow16_8 z * pow16_8 z := by rw [pow16_8_pow z hz]
    _ = _ := pow16_16_root z hz


theorem pow16_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_16 z * pow16_16 z = pow16_32_q z * f z + pow16_32 z + (131 : R) * pow16_32_mul_t z := by
  simp only [pow16_16, pow16_32_q, f, pow16_32, pow16_32_mul_t]
  
  ring

theorem pow16_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_16 z * pow16_16 z = pow16_32_q z * f z + pow16_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_32_mul_integer z


theorem pow16_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_16 z * pow16_16 z = pow16_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_32_mul z


theorem pow16_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 32 = pow16_32 z := by
  calc
    _ = u15 z ^ 16 * u15 z ^ 16 := by ring
    _ = pow16_16 z * pow16_16 z := by rw [pow16_16_pow z hz]
    _ = _ := pow16_32_root z hz


theorem pow16_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_32 z * pow16_32 z = pow16_64_q z * f z + pow16_64 z + (131 : R) * pow16_64_mul_t z := by
  simp only [pow16_32, pow16_64_q, f, pow16_64, pow16_64_mul_t]
  
  ring

theorem pow16_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_32 z * pow16_32 z = pow16_64_q z * f z + pow16_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_64_mul_integer z


theorem pow16_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_32 z * pow16_32 z = pow16_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_64_mul z


theorem pow16_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 64 = pow16_64 z := by
  calc
    _ = u15 z ^ 32 * u15 z ^ 32 := by ring
    _ = pow16_32 z * pow16_32 z := by rw [pow16_32_pow z hz]
    _ = _ := pow16_64_root z hz


theorem pow16_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_64 z * u15 z = pow16_65_q z * f z + pow16_65 z + (131 : R) * pow16_65_mul_t z := by
  simp only [pow16_64, u15, pow16_65_q, f, pow16_65, pow16_65_mul_t]
  simp only [pow15_131]
  ring

theorem pow16_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_64 z * u15 z = pow16_65_q z * f z + pow16_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_65_mul_integer z


theorem pow16_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_64 z * u15 z = pow16_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_65_mul z


theorem pow16_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 65 = pow16_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow16_64_pow z hz]
  exact pow16_65_root z hz


theorem pow16_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_65 z * pow16_65 z = pow16_130_q z * f z + pow16_130 z + (131 : R) * pow16_130_mul_t z := by
  simp only [pow16_65, pow16_130_q, f, pow16_130, pow16_130_mul_t]
  
  ring

theorem pow16_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_65 z * pow16_65 z = pow16_130_q z * f z + pow16_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_130_mul_integer z


theorem pow16_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_65 z * pow16_65 z = pow16_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_130_mul z


theorem pow16_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 130 = pow16_130 z := by
  calc
    _ = u15 z ^ 65 * u15 z ^ 65 := by ring
    _ = pow16_65 z * pow16_65 z := by rw [pow16_65_pow z hz]
    _ = _ := pow16_130_root z hz


theorem pow16_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_130 z * u15 z = pow16_131_q z * f z + pow16_131 z + (131 : R) * pow16_131_mul_t z := by
  simp only [pow16_130, u15, pow16_131_q, f, pow16_131, pow16_131_mul_t]
  simp only [pow15_131]
  ring

theorem pow16_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_130 z * u15 z = pow16_131_q z * f z + pow16_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_131_mul_integer z


theorem pow16_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_130 z * u15 z = pow16_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_131_mul z


theorem pow16_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 131 = pow16_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow16_130_pow z hz]
  exact pow16_131_root z hz


theorem iterate16 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 16) = u16 z := by
  calc
    _ = (z ^ (131 ^ 15)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u15 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate15 z hz)
    _ = _ := pow16_131_pow z hz

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers09
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem pow17_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z + (131 : R) * pow17_2_mul_t z := by
  simp only [u16, pow17_2_q, f, pow17_2, pow17_2_mul_t]
  simp only [pow16_131]
  ring

theorem pow17_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_2_mul_integer z


theorem pow17_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z * u16 z = pow17_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_2_mul z


theorem pow17_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 2 = pow17_2 z := by
  calc
    _ = u16 z ^ 1 * u16 z ^ 1 := by ring
    _ = u16 z * u16 z := by simp only [pow_one]
    _ = _ := pow17_2_root z hz


theorem pow17_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z + (131 : R) * pow17_4_mul_t z := by
  simp only [pow17_2, pow17_4_q, f, pow17_4, pow17_4_mul_t]
  
  ring

theorem pow17_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_4_mul_integer z


theorem pow17_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_2 z * pow17_2 z = pow17_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_4_mul z


theorem pow17_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 4 = pow17_4 z := by
  calc
    _ = u16 z ^ 2 * u16 z ^ 2 := by ring
    _ = pow17_2 z * pow17_2 z := by rw [pow17_2_pow z hz]
    _ = _ := pow17_4_root z hz


theorem pow17_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_4 z * pow17_4 z = pow17_8_q z * f z + pow17_8 z + (131 : R) * pow17_8_mul_t z := by
  simp only [pow17_4, pow17_8_q, f, pow17_8, pow17_8_mul_t]
  
  ring

theorem pow17_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_4 z * pow17_4 z = pow17_8_q z * f z + pow17_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_8_mul_integer z


theorem pow17_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_4 z * pow17_4 z = pow17_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_8_mul z


theorem pow17_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 8 = pow17_8 z := by
  calc
    _ = u16 z ^ 4 * u16 z ^ 4 := by ring
    _ = pow17_4 z * pow17_4 z := by rw [pow17_4_pow z hz]
    _ = _ := pow17_8_root z hz


theorem pow17_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_8 z * pow17_8 z = pow17_16_q z * f z + pow17_16 z + (131 : R) * pow17_16_mul_t z := by
  simp only [pow17_8, pow17_16_q, f, pow17_16, pow17_16_mul_t]
  
  ring

theorem pow17_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_8 z * pow17_8 z = pow17_16_q z * f z + pow17_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_16_mul_integer z


theorem pow17_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_8 z * pow17_8 z = pow17_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_16_mul z


theorem pow17_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 16 = pow17_16 z := by
  calc
    _ = u16 z ^ 8 * u16 z ^ 8 := by ring
    _ = pow17_8 z * pow17_8 z := by rw [pow17_8_pow z hz]
    _ = _ := pow17_16_root z hz


theorem pow17_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_16 z * pow17_16 z = pow17_32_q z * f z + pow17_32 z + (131 : R) * pow17_32_mul_t z := by
  simp only [pow17_16, pow17_32_q, f, pow17_32, pow17_32_mul_t]
  
  ring

theorem pow17_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_16 z * pow17_16 z = pow17_32_q z * f z + pow17_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_32_mul_integer z


theorem pow17_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_16 z * pow17_16 z = pow17_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_32_mul z


theorem pow17_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 32 = pow17_32 z := by
  calc
    _ = u16 z ^ 16 * u16 z ^ 16 := by ring
    _ = pow17_16 z * pow17_16 z := by rw [pow17_16_pow z hz]
    _ = _ := pow17_32_root z hz


theorem pow17_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_32 z * pow17_32 z = pow17_64_q z * f z + pow17_64 z + (131 : R) * pow17_64_mul_t z := by
  simp only [pow17_32, pow17_64_q, f, pow17_64, pow17_64_mul_t]
  
  ring

theorem pow17_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_32 z * pow17_32 z = pow17_64_q z * f z + pow17_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_64_mul_integer z


theorem pow17_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_32 z * pow17_32 z = pow17_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_64_mul z


theorem pow17_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 64 = pow17_64 z := by
  calc
    _ = u16 z ^ 32 * u16 z ^ 32 := by ring
    _ = pow17_32 z * pow17_32 z := by rw [pow17_32_pow z hz]
    _ = _ := pow17_64_root z hz


theorem pow17_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_64 z * u16 z = pow17_65_q z * f z + pow17_65 z + (131 : R) * pow17_65_mul_t z := by
  simp only [pow17_64, u16, pow17_65_q, f, pow17_65, pow17_65_mul_t]
  simp only [pow16_131]
  ring

theorem pow17_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_64 z * u16 z = pow17_65_q z * f z + pow17_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_65_mul_integer z


theorem pow17_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_64 z * u16 z = pow17_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_65_mul z


theorem pow17_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 65 = pow17_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow17_64_pow z hz]
  exact pow17_65_root z hz


theorem pow17_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_65 z * pow17_65 z = pow17_130_q z * f z + pow17_130 z + (131 : R) * pow17_130_mul_t z := by
  simp only [pow17_65, pow17_130_q, f, pow17_130, pow17_130_mul_t]
  
  ring

theorem pow17_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_65 z * pow17_65 z = pow17_130_q z * f z + pow17_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_130_mul_integer z


theorem pow17_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_65 z * pow17_65 z = pow17_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_130_mul z


theorem pow17_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 130 = pow17_130 z := by
  calc
    _ = u16 z ^ 65 * u16 z ^ 65 := by ring
    _ = pow17_65 z * pow17_65 z := by rw [pow17_65_pow z hz]
    _ = _ := pow17_130_root z hz


theorem pow17_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_130 z * u16 z = pow17_131_q z * f z + pow17_131 z + (131 : R) * pow17_131_mul_t z := by
  simp only [pow17_130, u16, pow17_131_q, f, pow17_131, pow17_131_mul_t]
  simp only [pow16_131]
  ring

theorem pow17_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_130 z * u16 z = pow17_131_q z * f z + pow17_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_131_mul_integer z


theorem pow17_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_130 z * u16 z = pow17_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_131_mul z


theorem pow17_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 131 = pow17_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow17_130_pow z hz]
  exact pow17_131_root z hz


theorem iterate17 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 17) = u17 z := by
  calc
    _ = (z ^ (131 ^ 16)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u16 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate16 z hz)
    _ = _ := pow17_131_pow z hz

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Result
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem bezout17_integer {R : Type*} [CommRing R] (z : R) :
    a17 z * f z + b17 z * (u17 z - z) = g17 z + (131 : R) * bezout17_t z := by
  simp only [a17, b17, f, u17, g17, bezout17_t]
  simp only [pow17_131]
  ring

theorem bezout17 {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    a17 z * f z + b17 z * (u17 z - z) = g17 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using bezout17_integer z


theorem factor17_f_integer {R : Type*} [CommRing R] (z : R) :
    f z = g17 z * div17_f z + (131 : R) * factor17_f_t z := by
  simp only [f, g17, div17_f, factor17_f_t]
  
  ring

theorem factor17_f {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    f z = g17 z * div17_f z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using factor17_f_integer z


theorem factor17_u17_integer {R : Type*} [CommRing R] (z : R) :
    (u17 z - z) = g17 z * div17_u17 z + (131 : R) * factor17_u17_t z := by
  simp only [u17, g17, div17_u17, factor17_u17_t]
  simp only [pow17_131]
  ring

theorem factor17_u17 {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    (u17 z - z) = g17 z * div17_u17 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using factor17_u17_integer z


theorem separable_bezout_integer {R : Type*} [CommRing R] (z : R) :
    da z * f z + db z * df z = 1 + (131 : R) * separable_bezout_t z := by
  simp only [da, db, df, f, separable_bezout_t]
  
  ring

theorem separable_bezout {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    da z * f z + db z * df z = 1 := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using separable_bezout_integer z

end DimensionTen.Mod131

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod131

lemma degree_g {R : Type*} [CommRing R] [Nontrivial R] :
    (g17 (X : R[X])).IsMonicOfDegree 18 := by
  unfold g17
  repeat' apply horner_monic_degree
  exact ⟨natDegree_one, monic_one⟩

lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by
  simp only [f, map_add, map_mul, map_ofNat, map_one]

lemma map_g17 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (g17 z) = g17 (φ z) := by
  simp only [g17, map_add, map_mul, map_ofNat, map_one]

lemma derivative_identity {R : Type*} [CommRing R] :
    Polynomial.derivative (f (X : R[X])) = df X + (131 : R[X]) * derivative_extra X := by
  simp only [f, df, derivative_extra, derivative_add, derivative_mul, derivative_X,
    derivative_ofNat, derivative_one]
  ring

lemma separable_f {k : Type*} [Field k] [CharP k 131] :
    (f (X : k[X])).Separable := by
  change IsCoprime _ _
  have h : (131 : k[X]) = 0 := CharP.cast_eq_zero _ 131
  rw [derivative_identity, h, zero_mul, add_zero]
  exact ⟨da X, db X, separable_bezout _⟩

lemma fixed_iff_g_zero {k : Type*} [Field k] [CharP k 131] (z : k) (hz : f z = 0) :
    z ^ (131 ^ 17) = z ↔ g17 z = 0 := by
  rw [iterate17 z hz]
  constructor
  · intro h
    have hb := bezout17 z
    simpa only [hz, mul_zero, h, sub_self, zero_add] using hb.symm
  · intro h
    apply sub_eq_zero.mp
    rw [factor17_u17, h, zero_mul]

end DimensionTen.Mod131

end
end

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_RootPermutation
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial
namespace DimensionTen


theorem card_fixed_of_factor {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hr : Function.Injective r) (σ : Equiv.Perm ι)
    (f g : k[X]) (hf : f = ∏ i, (X - C (r i))) (hs : f.Separable)
    (hd : g ∣ f) (hroot : ∀ i, g.eval (r i) = 0 ↔ σ i = i) :
    Fintype.card {i : ι // σ i = i} = g.natDegree := by
  classical
  have hf0 : f ≠ 0 := by rw [hf]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
  have hg0 : g ≠ 0 := ne_zero_of_dvd_ne_zero hf0 hd
  have hsplit : f.Splits := by rw [hf]; exact Splits.prod (fun _ _ => Splits.X_sub_C _)
  have hgr : ∀ x : k, g.eval x = 0 → ∃ i, r i = x := by
    intro x hx
    have hx' : f.eval x = 0 := by
      obtain ⟨q, rfl⟩ := hd
      simp [eval_mul, hx]
    rw [hf, eval_prod] at hx'
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hx'
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
    exact ⟨i, hi.symm⟩
  let u : {i : ι // σ i = i} → g.rootSet k :=
    fun i => ⟨r i, mem_rootSet.mpr ⟨hg0, by simpa using (hroot i).mpr i.property⟩⟩
  have hu : Function.Injective u := by
    intro i j h
    apply Subtype.ext
    apply hr
    exact congrArg Subtype.val h
  have hus : Function.Surjective u := by
    intro x
    have hx : g.eval (x : k) = 0 := by simpa using (mem_rootSet.mp x.property).2
    obtain ⟨i, hi⟩ := hgr x hx
    refine ⟨⟨i, (hroot i).mp (hi ▸ hx)⟩, ?_⟩
    exact Subtype.ext hi
  let e := Equiv.ofBijective u ⟨hu, hus⟩
  rw [Fintype.card_congr e]
  exact card_rootSet_eq_natDegree (hs.of_dvd hd) (by simpa using (hsplit.of_dvd hf0 hd))

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ModularPermutations
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial
namespace DimensionTen

lemma root_of_product {k ι : Type*} [Field k] [Fintype ι]
    (r : ι → k) (f : k[X]) (hf : f = ∏ i, (X - C (r i))) (i : ι) :
    f.eval (r i) = 0 := by
  classical
  rw [hf, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

lemma eval_mod131_f {k : Type*} [CommRing k] (x : k) :
    (Mod131.f (X : k[X])).eval x = Mod131.f x :=
  (Mod131.map_f (evalRingHom x) X).trans (congrArg Mod131.f (eval_X))

lemma eval_mod131_g {k : Type*} [CommRing k] (x : k) :
    (Mod131.g17 (X : k[X])).eval x = Mod131.g17 x :=
  (Mod131.map_g17 (evalRingHom x) X).trans (congrArg Mod131.g17 (eval_X))

lemma fixed_mod131_s2_oai {k ι : Type*} [Field k] [CharP k 131] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hinj : Function.Injective r) (π : Equiv.Perm ι)
    (hfact : Mod131.f X = ∏ i, (X - C (r i)))
    (hfrob : ∀ i, r (π i) = r i ^ 131) :
    Fintype.card {i : ι // (π ^ 17) i = i} = 18 := by
  have hfroot (i : ι) : Mod131.f (r i) = 0 := by
    rw [← eval_mod131_f]; exact root_of_product r _ hfact i
  have hfix (i : ι) : (Mod131.g17 (X : k[X])).eval (r i) = 0 ↔ (π ^ 17) i = i := by
    rw [eval_mod131_g, ← Mod131.fixed_iff_g_zero _ (hfroot i),
      ← iterate_pow_perm π r 131 hfrob 17 i, hinj.eq_iff]
  have hd : Mod131.g17 (X : k[X]) ∣ Mod131.f X :=
    ⟨Mod131.div17_f X, Mod131.factor17_f X⟩
  exact (card_fixed_of_factor r hinj (π ^ 17) _ _ hfact Mod131.separable_f hd hfix).trans
    Mod131.degree_g.natDegree_eq

end DimensionTen

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.DimensionTen.fixed_mod131_s2_oai.{u_1, u_2} := @OAI.DimensionTen.fixed_mod131_s2_oai.{u_1, u_2}
