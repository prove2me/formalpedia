-- Prove2me | solution 1 for GlobalTheory.SW.eq_of_thS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:34:40.621154+00:00
-- url     : https://prove2.me/submissions/debca1c1-9812-4024-bf0c-0609a5200b2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffEqZeroOfHasSumMFourierOrthonormalImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Theorems.Thm_GlobalTheory_SW_exists_int_div_of_intM
import Theorems.Thm_GlobalTheory_SW_SiegelSum_summable_norm_thetaTerm
import Theorems.Thm_GlobalTheory_coeff_eq_zero_of_fourier_series_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  intro κ ι _ _ _ φ ψ hφ hψ τ hτ h
  obtain ⟨R, hR, hRφ, -⟩ := id hφ
  obtain ⟨S, hS, hSψ, -⟩ := id hψ
  have hN : (((R * S : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  have hNC : (((R * S : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  let e : (κ × ι → ℤ) → Matrix κ ι ℚ := fun s =>
    Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)
  have he : Function.Injective e := by
    intro s t hst
    funext p
    have := congrFun (congrFun hst p.1) p.2
    simp only [e, Matrix.of_apply] at this
    have := (div_left_inj' hN).1 this
    exact_mod_cast this
  have hrange : ∀ x, φ x - ψ x ≠ 0 → x ∈ Set.range e := by
    intro x hx
    by_cases h1 : φ x = 0
    · have h2 : ψ x ≠ 0 := by
        intro h2; exact hx (by rw [h1, h2, sub_zero])
      obtain ⟨s, hs⟩ := exists_int_div_of_intM S R hS hR x (hSψ x h2)
      exact ⟨s, by rw [← hs, Nat.mul_comm S R]⟩
    · exact exists_int_div_of_intM R S hR hS x (hRφ x h1)
  let E : (κ → ι → ℂ) → Matrix κ ι ℚ → ℂ := fun ζ x =>
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))
  have hsφ : ∀ ζ, Summable fun x => φ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ).of_norm
  have hsψ : ∀ ζ, Summable fun x => ψ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι ψ hψ τ hτ ζ).of_norm
  have hs : ∀ ζ, Summable fun x => (φ x - ψ x) * E ζ x := fun ζ => by
    simpa only [sub_mul] using (hsφ ζ).sub (hsψ ζ)
  have hz : ∀ ζ, ∑' x, (φ x - ψ x) * E ζ x = 0 := fun ζ => by
    simp only [sub_mul]
    rw [(hsφ ζ).tsum_sub (hsψ ζ)]
    exact sub_eq_zero.2 (h ζ)
  have key := GlobalTheory.coeff_eq_zero_of_fourier_series_eq_zero (κ × ι)
    (fun s => (φ (e s) - ψ (e s)) * E 0 (e s))
    (((hs 0).comp_injective he).norm) (by
      intro y
      have h0 := hz (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ))
      rw [← he.tsum_eq (f := fun x => (φ x - ψ x) * E (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) x)
        (by
          intro x hx
          exact hrange x (left_ne_zero_of_mul hx))] at h0
      rw [← h0]
      refine tsum_congr fun s => ?_
      rw [mul_assoc]
      congr 1
      simp only [E]
      rw [← Complex.exp_add]
      congr 1
      have : ∀ k, qv (e s k) ⬝ᵥ (fun i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) =
          ∑ i, (s (k, i) : ℂ) * (y (k, i) : ℂ) := by
        intro k
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [qv, e, Matrix.of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
        field_simp
      simp only [this, Pi.zero_apply, dotProduct_zero, mul_zero, add_zero, Finset.sum_add_distrib,
        ← Finset.mul_sum, Fintype.sum_prod_type]
      ring)
  funext x
  by_contra hx
  obtain ⟨s, rfl⟩ := hrange x (sub_ne_zero.2 hx)
  have := key s
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hx (sub_eq_zero.1 h1)
  · exact Complex.exp_ne_zero _ h1
end GlobalTheory.SW
