-- Prove2me | solution 1 for ImpactInvesting.Portfolio.regression_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:30:05.223982+00:00
-- url     : https://prove2.me/submissions/0c4824ee-d25f-4579-9ebe-21b1805e6bdf

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_Portfolio_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open ImpactInvesting.Portfolio

theorem solution {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X α : Fin N → Ω → ℝ) (σα ρ : ℝ) (hA1 : IsA1 P X α σα ρ) (hσα : 0 < σα)
    (hρ₁ : -1 < ρ) (hρ₂ : ρ < 1) :
    (∀ i, P.map (fun ω => α i ω - ρ * σα * X i ω) =
        gaussianReal 0 (σα ^ 2 * (1 - ρ ^ 2)).toNNReal) ∧
    iIndepFun (fun k : Fin N ⊕ Fin N =>
        Sum.elim (fun i => X i) (fun i ω => α i ω - ρ * σα * X i ω) k) P := by
  set c : ℝ := ρ * σα with hc
  have hpair := hA1.gaussian
  have hGX : ∀ i, HasGaussianLaw (X i) P := fun i => (hpair i).fst
  have hGα : ∀ i, HasGaussianLaw (α i) P := fun i => (hpair i).snd
  have hmX : ∀ i, MemLp (X i) 2 P := fun i => (hGX i).memLp_two
  have hmα : ∀ i, MemLp (α i) 2 P := fun i => (hGα i).memLp_two
  have hGe : ∀ i, HasGaussianLaw (fun ω => α i ω - c * X i ω) P := by
    intro i
    have := (hpair i).map_fun (ContinuousLinearMap.snd ℝ ℝ ℝ - c • ContinuousLinearMap.fst ℝ ℝ ℝ)
    simpa using this
  have hme : ∀ i, MemLp (fun ω => α i ω - c * X i ω) 2 P := fun i => (hGe i).memLp_two
  -- mean and variance of the residuals
  have hmean : ∀ i, ∫ ω, (α i ω - c * X i ω) ∂P = 0 := by
    intro i
    rw [integral_sub (hGα i).integrable ((hGX i).integrable.const_mul c), integral_const_mul]
    have h1 := hA1.mean_α i
    have h2 := hA1.mean_X i
    simp only [h1, h2]
    ring
  have hvar : ∀ i, Var[fun ω => α i ω - c * X i ω; P] = σα ^ 2 * (1 - ρ ^ 2) := by
    intro i
    rw [variance_fun_sub (hmα i) ((hmX i).const_mul c), variance_const_mul,
      covariance_const_mul_right, covariance_comm, hA1.cov_Xα i, hA1.var_α i, hA1.var_X i]
    simp only [hc]
    ring
  refine ⟨fun i => ?_, ?_⟩
  · have := (hGe i).map_eq_gaussianReal
    rw [this, hmean i, hvar i]
  · have hW : HasGaussianLaw (fun ω i => (X i ω, α i ω)) P :=
      iIndepFun.hasGaussianLaw hpair hA1.indep
    let Lk : Fin N ⊕ Fin N → ((Fin N → ℝ × ℝ) →L[ℝ] ℝ) := fun k =>
      Sum.elim (fun i => (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i))
        (fun i => (ContinuousLinearMap.snd ℝ ℝ ℝ - c • ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.proj i)) k
    let L : (Fin N → ℝ × ℝ) →L[ℝ] (Fin N ⊕ Fin N → ℝ) := ContinuousLinearMap.pi Lk
    have hY : HasGaussianLaw (fun ω k =>
        (Sum.elim (fun i => X i) (fun i ω => α i ω - c * X i ω) k : Ω → ℝ) ω) P := by
      have := hW.map_fun L
      have e : (fun ω (k : Fin N ⊕ Fin N) =>
          (Sum.elim (fun i => X i) (fun i ω => α i ω - c * X i ω) k : Ω → ℝ) ω) =
          fun ω => L (fun i => (X i ω, α i ω)) := by
        funext ω k
        rcases k with i | i <;> simp [L, Lk]
      rw [e]
      exact this
    have hind : ∀ i j, i ≠ j → IndepFun (fun ω => (X i ω, α i ω)) (fun ω => (X j ω, α j ω)) P :=
      fun i j h => hA1.indep.indepFun h
    have mres : Measurable (fun p : ℝ × ℝ => p.2 - c * p.1) := by fun_prop
    have hXX : ∀ i j, i ≠ j → IndepFun (X i) (X j) P := fun i j h =>
      (hind i j h).comp measurable_fst measurable_fst
    have hXe : ∀ i j, i ≠ j → IndepFun (X i) (fun ω => α j ω - c * X j ω) P := fun i j h =>
      (hind i j h).comp measurable_fst mres
    have hee : ∀ i j, i ≠ j → IndepFun (fun ω => α i ω - c * X i ω)
        (fun ω => α j ω - c * X j ω) P := fun i j h =>
      (hind i j h).comp mres mres
    have hXeSame : ∀ i, cov[X i, fun ω => α i ω - c * X i ω; P] = 0 := by
      intro i
      rw [covariance_fun_sub_right (hmX i) (hmα i) ((hmX i).const_mul c),
        covariance_const_mul_right, covariance_self (hGX i).aemeasurable, hA1.cov_Xα i,
        hA1.var_X i]
      simp only [hc]
      ring
    have hcov : ∀ k l : Fin N ⊕ Fin N, k ≠ l →
        cov[(Sum.elim (fun i => X i) (fun i ω => α i ω - c * X i ω) k : Ω → ℝ),
          (Sum.elim (fun i => X i) (fun i ω => α i ω - c * X i ω) l : Ω → ℝ); P] = 0 := by
      rintro (i | i) (j | j) hkl
      · have hij : i ≠ j := fun h => hkl (by rw [h])
        exact (hXX i j hij).covariance_eq_zero (hmX i) (hmX j)
      · by_cases hij : i = j
        · subst hij; exact hXeSame i
        · exact (hXe i j hij).covariance_eq_zero (hmX i) (hme j)
      · by_cases hij : i = j
        · subst hij
          show cov[fun ω => α i ω - c * X i ω, X i; P] = 0
          rw [covariance_comm]; exact hXeSame i
        · show cov[fun ω => α i ω - c * X i ω, X j; P] = 0
          exact (hXe j i (Ne.symm hij)).symm.covariance_eq_zero (hme i) (hmX j)
      · have hij : i ≠ j := fun h => hkl (by rw [h])
        exact (hee i j hij).covariance_eq_zero (hme i) (hme j)
    exact hY.iIndepFun_of_covariance_eq_zero hcov
