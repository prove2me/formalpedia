-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.geom_sum_int_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:21.582096+00:00
-- url     : https://prove2.me/submissions/8830f55c-3261-4c95-b0e7-32c415bfc0e4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GeomSumIntLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic
namespace GlobalTheory.CompanionTheory.Adelic
theorem _root_.solution (D M : ℕ) (hD : 0 < D) (hM : 1 ≤ M) (x₀ C : ℝ) :
    ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * D * M := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.exp (-a) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1q : 0 < 1 - q := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max C 0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact le_max_right _ _
  have hCK : C ≤ K := by rw [hK]; exact le_max_left _ _
  refine ⟨K * Real.exp (-a * x₀) / (1 - q), fun r hr => ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, n₀ = ⌈x₀ - Real.log r⌉ := ⟨_, rfl⟩
  have hn₀le : x₀ - Real.log r ≤ n₀ := by rw [hn₀]; exact Int.le_ceil _
  have hr2 : (0 : ℝ) < r ^ (2 * D) := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * r ^ (2 * D) * Real.exp (-a * n₀) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.exp_pos (-a * n₀); positivity

  have hsupp : Function.support (fun j : ℤ =>
      (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ))))) ⊆
      Set.range (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro j hj
    have hnot : ¬ ((j : ℝ) + Real.log r < x₀) := by
      intro h
      apply hj
      simp [h]
    have hge : n₀ ≤ j := by
      rw [hn₀]
      apply Int.ceil_le.mpr
      linarith [not_lt.mp hnot]
    refine ⟨(j - n₀).toNat, ?_⟩
    have : (((j - n₀).toNat : ℕ) : ℤ) = j - n₀ := Int.toNat_of_nonneg (by omega)
    simp only [this]
    omega
  have hinj : Function.Injective (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro m n h
    simpa using h
  rw [← hinj.tsum_eq hsupp]

  have hterm : ∀ n : ℕ,
      (if (((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))) ≤
        ENNReal.ofReal (A * q ^ n) := by
    intro n
    split_ifs with h
    · simp
    · rw [← ENNReal.ofReal_mul' (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hr' : r ^ (2 * D) = Real.exp (((2 * D : ℕ) : ℝ) * Real.log r) := by
        rw [Real.exp_nat_mul, Real.exp_log hr]
      have hq' : q ^ n = Real.exp ((n : ℝ) * (-a)) := by
        rw [hq, Real.exp_nat_mul]
      have key : Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
          Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ))) =
          r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        rw [hr', hq', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ha]
        congr 1
        push_cast
        ring
      have hpos : 0 ≤ r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        have := Real.exp_pos (-a * n₀)
        positivity
      calc C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
            Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))
          = C * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) := by rw [mul_assoc, key]
        _ ≤ K * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) :=
            mul_le_mul_of_nonneg_right hCK hpos
        _ = A * q ^ n := by rw [hA]; ring
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hsum : Summable (fun n : ℕ => A * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left A
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  apply ENNReal.ofReal_le_ofReal
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

  have hexp : Real.exp (-a * n₀) ≤ Real.exp (-a * x₀) * r ^ (2 * D * M) := by
    have hr' : r ^ (2 * D * M) = Real.exp (((2 * D * M : ℕ) : ℝ) * Real.log r) := by
      rw [Real.exp_nat_mul, Real.exp_log hr]
    rw [hr', ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : (((2 * D * M : ℕ) : ℝ)) = a := by rw [ha]; push_cast; ring
    rw [hc]
    nlinarith [mul_le_mul_of_nonneg_left hn₀le ha0.le]
  have hpow : r ^ (2 * D * (M + 1)) = r ^ (2 * D) * r ^ (2 * D * M) := by
    rw [← pow_add]
    congr 1
    ring
  have hAle : A ≤ K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1)) := by
    rw [hA, hpow]
    calc K * r ^ (2 * D) * Real.exp (-a * n₀)
        ≤ K * r ^ (2 * D) * (Real.exp (-a * x₀) * r ^ (2 * D * M)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = K * Real.exp (-a * x₀) * (r ^ (2 * D) * r ^ (2 * D * M)) := by ring
  calc A * (1 - q)⁻¹
      ≤ (K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1))) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_right hAle (inv_nonneg.mpr h1q.le)
    _ = K * Real.exp (-a * x₀) / (1 - q) * r ^ (2 * D * (M + 1)) := by
        rw [div_eq_mul_inv]; ring
end GlobalTheory.CompanionTheory.Adelic
