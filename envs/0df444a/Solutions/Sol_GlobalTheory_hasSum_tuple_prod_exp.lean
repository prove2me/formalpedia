-- Prove2me | solution 1 for GlobalTheory.hasSum_tuple_prod_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:51.157655+00:00
-- url     : https://prove2.me/submissions/15259166-4916-4e97-bfd9-3797ea845621

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
private theorem hasSum_prod_fin_pow {ι : Type} (z : ι → ℂ) (g : ℂ)
    (hz : Summable fun i => ‖z i‖) (h : HasSum z g) (n : ℕ) :
    HasSum (fun f : Fin n → ι => ∏ k, z (f k)) (g ^ n) ∧
      Summable fun f : Fin n → ι => ‖∏ k, z (f k)‖ := by
  induction n with
  | zero =>
    refine ⟨?_, (hasSum_fintype _).summable⟩
    simpa using hasSum_fintype (fun f : Fin 0 → ι => ∏ k, z (f k))
  | succ n ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    let e : (ι × (Fin n → ι)) ≃ (Fin (n + 1) → ι) := Fin.consEquiv (fun _ : Fin (n + 1) => ι)
    have key : ∀ x : ι × (Fin n → ι), (∏ k, z (e x k)) = z x.1 * ∏ k, z (x.2 k) := by
      intro x
      change ∏ k, z ((Fin.cons x.1 x.2 : Fin (n + 1) → ι) k) = _
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hfun : (fun f : Fin (n + 1) → ι => ∏ k, z (f k)) ∘ e =
        fun x : ι × (Fin n → ι) => z x.1 * ∏ k, z (x.2 k) := funext key
    have hnorm : (fun f : Fin (n + 1) → ι => ‖∏ k, z (f k)‖) ∘ e =
        fun x : ι × (Fin n → ι) => ‖z x.1‖ * ‖∏ k, z (x.2 k)‖ := by
      funext x
      rw [← norm_mul, ← key x]
      rfl
    refine ⟨?_, ?_⟩
    · have H : HasSum (fun x : ι × (Fin n → ι) => z x.1 * ∏ k, z (x.2 k)) (g * g ^ n) :=
        HasSum.mul (f := z) (g := fun f : Fin n → ι => ∏ k, z (f k)) h ih₁
          (summable_mul_of_summable_norm (f := z) (g := fun f : Fin n → ι => ∏ k, z (f k)) hz ih₂)
      rw [← hfun] at H
      rw [pow_succ']
      exact (Equiv.hasSum_iff e).mp H
    · have H : Summable (fun x : ι × (Fin n → ι) => ‖z x.1‖ * ‖∏ k, z (x.2 k)‖) :=
        Summable.mul_of_nonneg (f := fun i => ‖z i‖) (g := fun f : Fin n → ι => ‖∏ k, z (f k)‖)
          hz ih₂ (fun i => norm_nonneg (z i)) (fun f => norm_nonneg _)
      rw [← hnorm] at H
      exact (Equiv.summable_iff e).mp H
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {ι : Type} (z : ι → ℂ) (g : ℂ) (h : HasSum z g) :
    HasSum (fun p : (Σ n : ℕ, Fin n → ι) => (∏ k, z (p.2 k)) / (p.1.factorial : ℂ))
      (Complex.exp g) := by
  have hz : Summable fun i => ‖z i‖ := summable_norm_iff.mpr h.summable
  have hz' : HasSum (fun i => ((‖z i‖ : ℝ) : ℂ)) ((∑' i, ‖z i‖ : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr hz.hasSum
  have hzn : Summable fun i => ‖((‖z i‖ : ℝ) : ℂ)‖ := by
    simpa using hz
  have fibr : ∀ n, HasSum (fun f : Fin n → ι => ‖∏ k, z (f k)‖) ((∑' i, ‖z i‖) ^ n) := by
    intro n
    have h1 := (hasSum_prod_fin_pow _ _ hzn hz' n).1
    have h2 : (fun f : Fin n → ι => ∏ k, ((‖z (f k)‖ : ℝ) : ℂ)) =
        fun f => ((‖∏ k, z (f k)‖ : ℝ) : ℂ) := by
      funext f
      rw [norm_prod, Complex.ofReal_prod]
    rw [h2, ← Complex.ofReal_pow] at h1
    exact Complex.hasSum_ofReal.mp h1
  have hsum : Summable fun p : (Σ n : ℕ, Fin n → ι) =>
      (∏ k, z (p.2 k)) / (p.1.factorial : ℂ) := by
    apply Summable.of_norm
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun n => ?_, ?_⟩
    · simp only [norm_div, Complex.norm_natCast]
      exact (fibr n).summable.div_const _
    · simp only [norm_div, Complex.norm_natCast]
      have hn : ∀ n : ℕ, ∑' f : Fin n → ι, ‖∏ k, z (f k)‖ / (n.factorial : ℝ) =
          (∑' i, ‖z i‖) ^ n / n.factorial := fun n => ((fibr n).div_const _).tsum_eq
      simp only [hn]
      exact Real.summable_pow_div_factorial _
  have hexp : HasSum (fun n : ℕ => g ^ n / (n.factorial : ℂ)) (Complex.exp g) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp g
  exact HasSum.sigma_of_hasSum hexp
    (fun n => ((hasSum_prod_fin_pow z g hz h n).1.div_const (n.factorial : ℂ))) hsum
end _root_.GlobalTheory
end GlobalTheory
