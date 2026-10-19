-- Prove2me | solution 1 for MazurTransfer.Order13CyclotomicReflectionGeneratorOrbit.mapParameter_generator
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T22:35:42.57075+00:00
-- url     : https://prove2.me/submissions/359c4b3f-8b9b-4a61-9868-650549492ef1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the primitive-root transformation z -> z^2 sends the
literal cyclotomic reflection parameter to its fifth diamond iterate.
Named downstream consumer: the exact arithmetic13 character on the SAME
actual cyclotomic quotient kernel.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ReflectionDiamondParameterOriginalDataAndConstructorCertificatesMinimalPublicNamespaceV220261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
noncomputable section
universe u
open MazurTransfer.Order13CyclotomicReflectionCoefficients MazurTransfer.Order13ReflectionParameter
open MazurTransfer.Order13ReflectionParameterArithmetic MazurTransfer.Order13ReflectionSexticSymmetry
open MazurTransfer.Order13DiamondSexticSymmetry MazurTransfer.Order13ActualReflectionCoefficientCovariance
namespace MazurTransfer.CyclotomicReflectionGeneratorOrbitProofHelpers20261018
section Diamond
variable {F : Type u} [Field F]
theorem diamondX_sq (x : F) (hx : x ≠ 0) (hd : x + 1 ≠ 0) :
    diamondX (diamondX x) = -(x + 1) / x := by
  dsimp [diamondX]
  field_simp [hx, hd] <;> ring

theorem diamondX_cube (x : F) (hx : x ≠ 0) (hd : x + 1 ≠ 0) :
    diamondX (diamondX (diamondX x)) = x := by
  rw [diamondX_sq x hx hd]
  dsimp [diamondX]
  field_simp [hx] <;> ring

end Diamond
variable {K : Type u} [Field K]
theorem diamondParameter_cube_t (a : ReflectionParameter K) :
    (diamondParameter (diamondParameter (diamondParameter a))).t = a.t :=
  diamondX_cube a.t (parameter_t_ne_zero a) (parameter_t_add_one_ne_zero a)

theorem diamondParameter_cube_s (a : ReflectionParameter K) :
    (diamondParameter (diamondParameter (diamondParameter a))).s = -a.s := by
  change a.s / (a.t + 1) / (diamondX a.t + 1) /
    (diamondX (diamondX a.t) + 1) = -a.s
  rw [diamondX_sq a.t (parameter_t_ne_zero a) (parameter_t_add_one_ne_zero a)]
  dsimp [diamondX]
  field_simp [parameter_t_ne_zero a, parameter_t_add_one_ne_zero a]
  ring
def secondPeriod (z : K) : K := z ^ 2 + z ^ 3 + z ^ 10 + z ^ 11 - 1
def numerator (t : K) : K := 3 * t ^ 2 + 8 * t + 1

theorem period_power_certificate (z : K) :
    cubicPeriod (z ^ 2) - secondPeriod z = (z ^ 13 - 1) * (z ^ 11 + z ^ 3) := by
  dsimp [cubicPeriod, secondPeriod]
  ring

theorem period_orbit_certificate (z : K) :
    cubicPeriod z * secondPeriod z + cubicPeriod z + 1 =
      (z ^ 11 - z ^ 9 + z ^ 7 - z ^ 5 + z ^ 4 + z ^ 3 - z ^ 2 - z + 1) * cyclotomicSum z := by
  dsimp [cubicPeriod, secondPeriod, cyclotomicSum]
  ring

theorem numerator_orbit_certificate (z : K) :
    cubicPeriod z * numerator (secondPeriod z) - numerator (cubicPeriod z) =
      (3 * z ^ 22 + 3 * z ^ 21 - 3 * z ^ 20 - 3 * z ^ 19 + 3 * z ^ 18 + 3 * z ^ 17 -
        3 * z ^ 16 + 9 * z ^ 14 + 3 * z ^ 13 - 12 * z ^ 12 + 2 * z ^ 11 + 6 * z ^ 10 +
        z ^ 9 - 9 * z ^ 8 + 8 * z ^ 7 + 6 * z ^ 6 - 8 * z ^ 5 - z ^ 4 + 5 * z ^ 3 +
        z ^ 2 - 14 * z + 8) * cyclotomicSum z := by
  dsimp [cubicPeriod, secondPeriod, numerator, cyclotomicSum]
  ring

theorem gauss_orbit_certificate (z : K) :
    quadraticGauss (z ^ 2) + quadraticGauss z =
      (z ^ 13 - 1) * (z ^ 11 - z ^ 9 + z ^ 7 + z ^ 5 - z ^ 3 - z) := by
  dsimp [quadraticGauss]
  ring

theorem cubicPeriod_pow_two {z : K} (hz : IsPrimitiveRoot z 13) :
    cubicPeriod (z ^ 2) = -(cubicPeriod z + 1) / cubicPeriod z := by
  have hp := period_power_certificate z
  rw [hz.pow_eq_one, sub_self, zero_mul] at hp
  have hp' := sub_eq_zero.mp hp
  have ho := period_orbit_certificate z
  rw [cyclotomicSum_eq_zero hz, mul_zero, ← hp'] at ho
  have ht : cubicPeriod z ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_add, zero_add] at ho
    exact one_ne_zero ho
  apply (eq_div_iff ht).mpr
  linear_combination ho

theorem quadraticGauss_pow_two {z : K} (hz : IsPrimitiveRoot z 13) :
    quadraticGauss (z ^ 2) = -quadraticGauss z := by
  have h := gauss_orbit_certificate z
  rw [hz.pow_eq_one, sub_self, zero_mul] at h
  exact eq_neg_of_add_eq_zero_left h

theorem reflectionS_pow_two [CharZero K] {z : K} (hz : IsPrimitiveRoot z 13) :
    reflectionS (z ^ 2) = -reflectionS z / cubicPeriod z := by
  have hp := period_power_certificate z
  rw [hz.pow_eq_one, sub_self, zero_mul] at hp
  have hp' := sub_eq_zero.mp hp
  have hn := numerator_orbit_certificate z
  rw [cyclotomicSum_eq_zero hz, mul_zero, ← hp'] at hn
  have ht := parameter_t_ne_zero (cyclotomicParameter z hz)
  have hG := quadraticGauss_ne_zero hz
  dsimp [cyclotomicParameter] at ht
  change numerator (cubicPeriod (z ^ 2)) / quadraticGauss (z ^ 2) =
    -(numerator (cubicPeriod z) / quadraticGauss z) / cubicPeriod z
  rw [quadraticGauss_pow_two hz]
  field_simp [ht, hG]
  linear_combination -hn

def fifthParameter (a : ReflectionParameter K) : ReflectionParameter K :=
  diamondParameter (diamondParameter (diamondParameter (diamondParameter (diamondParameter a))))

theorem fifthParameter_t (a : ReflectionParameter K) :
    (fifthParameter a).t = -(a.t + 1) / a.t := by
  change diamondX (diamondX (diamondParameter (diamondParameter (diamondParameter a))).t) = _
  rw [diamondParameter_cube_t]
  exact diamondX_sq a.t (parameter_t_ne_zero a) (parameter_t_add_one_ne_zero a)

theorem fifthParameter_s (a : ReflectionParameter K) : (fifthParameter a).s = -a.s / a.t := by
  change (diamondParameter (diamondParameter (diamondParameter a))).s /
    ((diamondParameter (diamondParameter (diamondParameter a))).t + 1) /
    (diamondX (diamondParameter (diamondParameter (diamondParameter a))).t + 1) = _
  rw [diamondParameter_cube_t, diamondParameter_cube_s]
  dsimp [diamondX]
  field_simp [parameter_t_ne_zero a, parameter_t_add_one_ne_zero a]
  ring

theorem parameter_ext {a b : ReflectionParameter K} (ht : a.t = b.t) (hs : a.s = b.s) : a = b := by
  cases a
  cases b
  congr 1

variable [CharZero K]

theorem cyclotomicParameter_pow_two {z : K} (hz : IsPrimitiveRoot z 13) :
    cyclotomicParameter (z ^ 2) (hz.pow_of_coprime 2 (by decide)) = fifthParameter (cyclotomicParameter z hz) := by
  apply parameter_ext
  · exact (cubicPeriod_pow_two hz).trans (fifthParameter_t (cyclotomicParameter z hz)).symm
  · exact (reflectionS_pow_two hz).trans (fifthParameter_s (cyclotomicParameter z hz)).symm

end MazurTransfer.CyclotomicReflectionGeneratorOrbitProofHelpers20261018
open MazurTransfer.CyclotomicReflectionGeneratorOrbitProofHelpers20261018
variable {K : Type u} [Field K] [CharZero K]
theorem solution (σ : K ≃+* K) {z : K} (hz : IsPrimitiveRoot z 13)
    (hσ : σ z = z ^ 2) :
    mapParameter K σ (cyclotomicParameter z hz) = fifthParameter (cyclotomicParameter z hz) := by
  rw [← cyclotomicParameter_pow_two hz]
  apply parameter_ext
  · change σ (cubicPeriod z) = cubicPeriod (z ^ 2)
    simp only [cubicPeriod, map_add, map_pow, map_sub, map_one, hσ]
  · change σ (reflectionS z) = reflectionS (z ^ 2)
    simp only [reflectionS, cubicPeriod, quadraticGauss, map_add, map_pow, map_sub,
      map_one, map_ofNat, map_mul, map_div₀, hσ]

#print axioms solution
