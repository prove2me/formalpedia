-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig.exists_minimal_below
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:51.662436+00:00
-- url     : https://prove2.me/submissions/df0c7c75-045b-41be-9875-4b55e9e10f11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturatedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRingAltBis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartRegularAtConePoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Sig_renR_X_sub_one_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Sig_renR_sub_deh_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Sig_deh_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
theorem _root_.solution {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
    {𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)} (h𝔮 : 𝔮.IsPrime)
    (hD : SncRes.ideal (P ⊔ D) p ≤ 𝔮) :
    ∃ Q ∈ (P ⊔ D).minimalPrimes,
      (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) ∧ SncRes.ideal Q p ≤ 𝔮 := by
  classical
  have hle : P ⊔ D ≤ 𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _) :=
    fun g hg => hD (deh_mem p hg)
  haveI : (𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _)).IsPrime :=
    Ideal.comap_isPrime _ _
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨Q, hQ, fun k hX => ?_, ?_⟩
  · have h1 : bind₁ (SncRes.lift p) (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮 := hQle hX
    have h2 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
    rw [bind₁_X_right, h2] at h1
    exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · refine Ideal.map_le_iff_le_comap.2 (sup_le ?_ ?_)
    · intro f hf
      have h1 : bind₁ (SncRes.lift p) f ∈ 𝔮 := hQle hf
      have h2 := 𝔮.add_mem (hD (renR_sub_deh_mem (P ⊔ D) p f)) h1
      simpa using h2
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact hD (renR_X_sub_one_mem (P ⊔ D) p k)
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
