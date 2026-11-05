-- Prove2me | solution 1 for LasserreFC.FinConv.epsilon_feasible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:27:29.089794+00:00
-- url     : https://prove2.me/submissions/700c450e-c10c-42f5-b4d5-090b51e90e90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_Hierarchy
import Theorems.Thm_LasserreFC_FinConv_real_nullstellensatz
import Theorems.Thm_LasserreFC_FinConv_univariate_sos

open MvPolynomial LasserreFC.FinConv

theorem solution {n m1 m2 : ℕ} (P : POP n m1 m2) (fmin : ℝ)
    (hrep : ∃ q ∈ vanishingIdeal ℝ (realVariety P), ∃ σ1 ∈ qmod P, P.f - C fmin = q + σ1) :
    ∃ k0 : ℕ, ∀ ε : ℝ, 0 < ε → P.f - C (fmin - ε) ∈ trunc P k0 := by
  obtain ⟨q, hq, σ1, hσ1, hfq⟩ := hrep
  -- Real Nullstellensatz: q^{2e} + σ2 ∈ ⟨h⟩
  obtain ⟨e, σ2, hσ2, hI⟩ := real_nullstellensatz P q hq
  -- pass to e' = e + 1 ≥ 1 : q^{2(e+1)} + q^2 σ2 = q^2 (q^{2e} + σ2) ∈ ⟨h⟩
  set e' := e + 1 with he'
  set τ := q * q * σ2 with hτ
  have hτsos : IsSumSq τ := IsSumSq.mul (IsSumSq.mul_self q) hσ2
  have hI' : q ^ (2 * e') + τ ∈ Ideal.span (Set.range P.h) := by
    have : q ^ (2 * e') + τ = (q * q) * (q ^ (2 * e) + σ2) := by
      rw [he', hτ]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ hI
  obtain ⟨a, ha⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hI'
  -- univariate SOS polynomial s(t) = 1 + t + c t^{2e'}
  obtain ⟨c, hc, hs⟩ := univariate_sos e' (by omega)
  -- the representation of σ1
  obtain ⟨k1, hk1⟩ := Set.mem_iUnion.1 hσ1
  obtain ⟨σ0, σ, hσ0, hσ0d, hσj, hσ1eq⟩ := hk1
  set N : ℕ := q.totalDegree * (2 * e') + q.totalDegree + τ.totalDegree +
    ∑ i, (a i * P.h i).totalDegree with hN
  refine ⟨k1 + N, fun ε hε => ?_⟩
  set κ : ℝ := ε * c * (ε⁻¹) ^ (2 * e') with hκ
  have hκpos : 0 < κ := by positivity
  -- SOS-ness of ε s(q/ε) = ε + q + κ q^{2e'}
  have hmid : IsSumSq (C ε + q + C κ * q ^ (2 * e')) := by
    have hmap : IsSumSq (Polynomial.aeval (C ε⁻¹ * q)
        (1 + Polynomial.X + Polynomial.C c * Polynomial.X ^ (2 * e') : Polynomial ℝ)) := by
      have gen : ∀ p : Polynomial ℝ, IsSumSq p → IsSumSq (Polynomial.aeval (C ε⁻¹ * q) p) := by
        intro p hp
        induction hp with
        | zero => simp
        | sq_add b hs ih =>
          rw [map_add, map_mul]
          exact IsSumSq.sq_add _ ih
      exact gen _ hs
    have hsq : IsSumSq (C ε : MvPolynomial (Fin n) ℝ) := by
      have : (C ε : MvPolynomial (Fin n) ℝ) = C (Real.sqrt ε) * C (Real.sqrt ε) := by
        rw [← C_mul, Real.mul_self_sqrt hε.le]
      rw [this]; exact IsSumSq.mul_self _
    have heq : C ε * Polynomial.aeval (C ε⁻¹ * q)
        (1 + Polynomial.X + Polynomial.C c * Polynomial.X ^ (2 * e') : Polynomial ℝ) =
        C ε + q + C κ * q ^ (2 * e') := by
      simp only [map_add, map_one, Polynomial.aeval_X, map_mul, Polynomial.aeval_C, map_pow,
        MvPolynomial.algebraMap_eq]
      rw [hκ, mul_pow, ← C_pow, C_mul, C_mul]
      have h1 : (C ε : MvPolynomial (Fin n) ℝ) * C ε⁻¹ = 1 := by
        rw [← C_mul, mul_inv_cancel₀ hε.ne', C_1]
      linear_combination (q) * h1
    rw [← heq]; exact IsSumSq.mul hsq hmap
  have hκsq : IsSumSq (C κ * τ) := by
    have : (C κ : MvPolynomial (Fin n) ℝ) = C (Real.sqrt κ) * C (Real.sqrt κ) := by
      rw [← C_mul, Real.mul_self_sqrt hκpos.le]
    rw [this]; exact IsSumSq.mul (IsSumSq.mul_self _) hτsos
  -- degree bookkeeping
  have hqd : q.totalDegree ≤ N := by rw [hN]; omega
  have hqpd : (q ^ (2 * e')).totalDegree ≤ N := by
    refine (totalDegree_pow _ _).trans ?_
    rw [hN, mul_comm]; omega
  have hτd : τ.totalDegree ≤ N := by rw [hN]; omega
  have had : ∀ i, (a i * P.h i).totalDegree ≤ N := by
    intro i
    have : (a i * P.h i).totalDegree ≤ ∑ i, (a i * P.h i).totalDegree :=
      Finset.single_le_sum (f := fun i => (a i * P.h i).totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    rw [hN]; omega
  have hCmul : ∀ (r : ℝ) (p : MvPolynomial (Fin n) ℝ), (C r * p).totalDegree ≤ p.totalDegree := by
    intro r p
    refine (totalDegree_mul _ _).trans ?_
    simp
  refine ⟨∑ i, (C (-κ) * a i) * P.h i, ⟨fun i => C (-κ) * a i, rfl, fun i => ?_⟩,
    (σ0 + (C ε + q + C κ * q ^ (2 * e')) + C κ * τ) + ∑ j, σ j * P.g j,
    ⟨σ0 + (C ε + q + C κ * q ^ (2 * e')) + C κ * τ, σ, ?_, ?_, fun j => ?_, rfl⟩, ?_⟩
  · rw [mul_assoc]
    refine (hCmul _ _).trans ?_
    have := had i; omega
  · exact (hσ0.add hmid).add hκsq
  · refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le ?_ ((totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
        (max_le ?_ ?_)) ?_)))) ?_)
    · omega
    · simp
    · omega
    · exact (hCmul _ _).trans (by omega)
    · exact (hCmul _ _).trans (by omega)
  · obtain ⟨h1, h2⟩ := hσj j
    exact ⟨h1, h2.trans (by omega)⟩
  · have hsum : ∑ i, (C (-κ) * a i) * P.h i = C (-κ) * (q ^ (2 * e') + τ) := by
      rw [← ha, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    have hf : P.f = C fmin + q + σ1 := by linear_combination hfq
    rw [hf, hσ1eq, C_sub, C_neg]
    ring
