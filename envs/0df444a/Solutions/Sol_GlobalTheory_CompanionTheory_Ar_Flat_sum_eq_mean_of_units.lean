-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.sum_eq_mean_of_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:32:06.628923+00:00
-- url     : https://prove2.me/submissions/ddac9a48-0834-4d3b-af9b-9f363e4d73d2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ExistsEqMulMultOfUnits
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_exists_eq_mul_mult_of_units

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace GlobalTheory.CompanionTheory.Ar.Flat
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (d t : (F →+* ℂ) → ℝ),
      (∀ u : (𝓞 F)ˣ, ∑ σ : F →+* ℂ, Real.log ‖σ ((u : 𝓞 F) : F)‖ * d σ = 0) →
      (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) →
      ∑ σ : F →+* ℂ, t σ * d σ =
        (∑ σ : F →+* ℂ, t σ) / (Module.finrank ℚ F : ℝ) * ∑ σ : F →+* ℂ, d σ := by
  intro F _ _ d t hd ht
  classical
  have hfib : ∀ f : (F →+* ℂ) → ℝ, ∑ σ, f σ
      = ∑ w : InfinitePlace F, ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ :=
    fun f => (Finset.sum_fiberwise Finset.univ InfinitePlace.mk f).symm
  obtain ⟨c, hc⟩ := exists_eq_mul_mult_of_units F
    (fun w => ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), d σ) (by
      intro u
      have h1 := hd u
      rw [hfib] at h1
      refine Eq.trans ?_ h1
      apply Finset.sum_congr rfl
      intro w _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
      rw [InfinitePlace.apply])
  have ht' : ∀ σ : F →+* ℂ, t σ = t (InfinitePlace.mk σ).embedding := by
    intro σ
    have h2 : InfinitePlace.mk (InfinitePlace.mk σ).embedding = InfinitePlace.mk σ :=
      InfinitePlace.mk_embedding _
    rcases InfinitePlace.mk_eq_iff.mp h2 with h3 | h3
    · rw [h3]
    · have h4 := ht (InfinitePlace.mk σ).embedding
      rw [h3] at h4
      exact h4
  have hTfib : ∀ (w : InfinitePlace F) (f : (F →+* ℂ) → ℝ),
      ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), t σ * f σ
        = t w.embedding * ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ := by
    intro w f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
    rw [← ht' σ]
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hsum_d : ∑ σ, d σ = c * (Module.finrank ℚ F : ℝ) := by
    rw [hfib, ← InfinitePlace.sum_mult_eq, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact hc w
  have hsum_t : ∑ σ, t σ = ∑ w : InfinitePlace F, t w.embedding * (w.mult : ℝ) := by
    rw [hfib]
    apply Finset.sum_congr rfl
    intro w _
    have h5 := hTfib w (fun _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h5
    rw [h5, InfinitePlace.card_filter_mk_eq]
  have hsum_td : ∑ σ, t σ * d σ = c * ∑ σ, t σ := by
    conv_lhs => rw [hfib]
    rw [hsum_t, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [hTfib w d]
    have h6 := hc w
    rw [h6]
    ring
  rw [hsum_td, hsum_d, div_mul_eq_mul_div, eq_div_iff hn]
  ring
end GlobalTheory.CompanionTheory.Ar.Flat
