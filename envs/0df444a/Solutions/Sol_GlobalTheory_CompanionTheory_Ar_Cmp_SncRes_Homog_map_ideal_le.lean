-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.map_ideal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:44.64585+00:00
-- url     : https://prove2.me/submissions/2d048f32-9169-4ea1-bc63-2cf0c048e41d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChart
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_aeval_smul_of_isMultiHomog
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_chartSub_renC
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_aeval_algebraMap_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {L : Type} [CommRing L] [Algebra ℂ L] [Algebra (MvPolynomial (Σ k, ι k) ℂ) L]
  [IsScalarTower ℂ (MvPolynomial (Σ k, ι k) ℂ) L]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
theorem _root_.solution (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hS : IsMultiHomogIdeal S)
    (p : (k : K) → ι k) (c : K → L)
    (hc : ∀ k, c k * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X ⟨k, p k⟩) = 1) :
    (ideal S p).map (chartSub fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) ≤
      S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) := by
  rw [Ideal.map_le_iff_le_comap]
  unfold ideal
  rw [Ideal.map_le_iff_le_comap]
  intro h hh
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have key : ∀ h ∈ chartIdeal S p, aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) h ∈
      S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) := by
    obtain ⟨G, hG, rfl⟩ := hS
    intro h hh
    have hle : chartIdeal (Ideal.span G) p ≤
        (Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) (Ideal.span G)).comap
          (aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) :
            MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] L) := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le]
        intro g hg
        obtain ⟨b, hb⟩ := hG g hg
        rw [SetLike.mem_coe, Ideal.mem_comap, aeval_smul_of_isMultiHomog hb, aeval_algebraMap_X]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hg))
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap]
        simp [hc k]
    exact hle hh
  have e : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) h = renC (Σ k, ι k) h := rfl
  rw [e, chartSub_renC]
  exact key h hh
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
