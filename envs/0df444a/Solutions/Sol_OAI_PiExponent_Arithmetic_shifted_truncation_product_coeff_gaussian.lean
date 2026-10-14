-- Prove2me | solution 1 for OAI.PiExponent.Arithmetic.shifted_truncation_product_coeff_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T14:21:25.211021+00:00
-- url     : https://prove2.me/submissions/0a346b4d-4f4a-48bb-926a-2c89e6d27816

import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic

namespace OAI.PiExponent.Arithmetic

theorem dvd_lcmUpto_of_pos_le {k T : ℕ} (hk : 0 < k) (hkT : k ≤ T) :
    k ∣ Nat.lcmUpto T := by
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hk, hkT⟩)

theorem lcm_mul_log_coeff_gaussian (T k : ℕ) (hk : k ≤ T) :
    (Nat.lcmUpto T : ℂ) * PowerSeries.coeff k (PowerSeries.log ℂ) ∈
      GaussianInt.toComplex.range := by
  by_cases hk0 : k = 0
  · simp [hk0]
  obtain ⟨m, hm⟩ := dvd_lcmUpto_of_pos_le (Nat.pos_of_ne_zero hk0) hk
  refine ⟨((-1 : GaussianInt) ^ (k + 1)) * (m : GaussianInt), ?_⟩
  rw [PowerSeries.coeff_log, if_neg hk0, hm]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀, Nat.cast_mul]
  field_simp

theorem cleared_log_trunc_mem (T : ℕ) :
    Polynomial.C (Nat.lcmUpto T : ℂ) * PowerSeries.trunc T (PowerSeries.log ℂ) ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  apply (Polynomial.mem_map_range GaussianInt.toComplex).mpr
  intro k
  rw [Polynomial.coeff_C_mul, PowerSeries.coeff_trunc]
  split_ifs with hk
  · exact lcm_mul_log_coeff_gaussian T k hk.le
  · simp

theorem gaussian_C_mem (z : GaussianInt) :
    Polynomial.C (z : ℂ) ∈ (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  exact ⟨Polynomial.C z, by simp⟩

theorem cleared_shifted_log_trunc_mem (T q : ℕ) (z : GaussianInt) :
    Polynomial.C (Nat.lcmUpto T : ℂ) *
      (Polynomial.C (z : ℂ) + Polynomial.C (q : ℂ) *
        PowerSeries.trunc T (PowerSeries.log ℂ)) ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have hL : Polynomial.C (Nat.lcmUpto T : ℂ) ∈ S := by
    simp
  have hq : Polynomial.C (q : ℂ) ∈ S := by
    simp
  have hlog := cleared_log_trunc_mem T
  have h := S.add_mem (S.mul_mem hL (gaussian_C_mem z)) (S.mul_mem hq hlog)
  convert h using 1
  ring

theorem cleared_polynomial_power_mem (L e d : ℕ) (f : Polynomial ℂ) (hd : d ≤ e)
    (hf : Polynomial.C (L : ℂ) * f ∈ (Polynomial.mapRingHom GaussianInt.toComplex).range) :
    Polynomial.C ((L : ℂ) ^ e) * f ^ d ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have hL : Polynomial.C (L : ℂ) ∈ S := by
    simp
  have h := S.mul_mem (S.pow_mem hL (e - d)) (S.pow_mem hf d)
  have he : e = (e - d) + d := (Nat.sub_add_cancel hd).symm
  rw [he, map_pow, pow_add]
  simpa only [mul_pow, mul_assoc] using h

theorem cleared_polynomial_product_mem {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → Polynomial ℂ) (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, Polynomial.C (L i : ℂ) * f i ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range) :
    Polynomial.C (∏ i ∈ s, (L i : ℂ) ^ e i) * (∏ i ∈ s, f i ^ d i) ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have h := S.prod_mem (fun i hi => cleared_polynomial_power_mem (L i) (e i) (d i)
    (f i) (hd i hi) (hf i hi))
  simpa only [← Finset.prod_mul_distrib, map_prod] using h

theorem common_denominator_coeff_gaussian {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → Polynomial ℂ) (P : Polynomial GaussianInt)
    (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, Polynomial.C (L i : ℂ) * f i ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range) (k : ℕ) :
    (∏ i ∈ s, (L i : ℂ) ^ e i) *
      (P.map GaussianInt.toComplex * ∏ i ∈ s, f i ^ d i).coeff k ∈
      GaussianInt.toComplex.range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have hP : P.map GaussianInt.toComplex ∈ S := ⟨P, rfl⟩
  have h := S.mul_mem hP (cleared_polynomial_product_mem s L e d f hd hf)
  have he : P.map GaussianInt.toComplex *
      (Polynomial.C (∏ i ∈ s, (L i : ℂ) ^ e i) * ∏ i ∈ s, f i ^ d i) =
      Polynomial.C (∏ i ∈ s, (L i : ℂ) ^ e i) *
        (P.map GaussianInt.toComplex * ∏ i ∈ s, f i ^ d i) := by ring
  rw [he] at h
  have hc := (Polynomial.mem_map_range GaussianInt.toComplex).mp h k
  simpa only [Polynomial.coeff_C_mul] using hc

end OAI.PiExponent.Arithmetic

open OAI.PiExponent.Arithmetic

theorem solution {ι : Type*} (s : Finset ι)
    (T q e d : ι → ℕ) (z : ι → GaussianInt) (P : Polynomial GaussianInt)
    (hd : ∀ i ∈ s, d i ≤ e i) (k : ℕ) :
    (∏ i ∈ s, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (P.map GaussianInt.toComplex * ∏ i ∈ s,
        (Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
          PowerSeries.trunc (T i) (PowerSeries.log ℂ)) ^ d i).coeff k ∈
      GaussianInt.toComplex.range := by
  exact common_denominator_coeff_gaussian s (fun i => Nat.lcmUpto (T i)) e d _ P hd
    (fun i hi => cleared_shifted_log_trunc_mem (T i) (q i) (z i)) k
