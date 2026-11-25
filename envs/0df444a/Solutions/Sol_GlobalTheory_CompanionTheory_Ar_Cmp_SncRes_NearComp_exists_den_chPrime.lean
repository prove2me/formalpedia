-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.exists_den_chPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:37:10.508595+00:00
-- url     : https://prove2.me/submissions/2be1693f-495a-429f-8a45-3dd7ab1c47a3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSup
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartRegularWithBoundaryChoice
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_mul_mem_of_algebraMap_locRing_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_mk_locRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp
theorem _root_.solution {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (r : MvPolynomial (Fin m) ℂ) :
    ∃ s : MvPolynomial (Fin m) ℂ, eval t s ≠ 0 ∧ ∀ w : Fin m → ℂ, (∀ h ∈ I, eval w h = 0) →
      eval w s ≠ 0 → eval w r = 0 → ∀ g ∈ Par.chPrime I t r, eval w g = 0 := by
  classical
  have hgen : ∀ g ∈ Par.chPrime I t r, ∃ u : MvPolynomial (Fin m) ℂ, eval t u ≠ 0 ∧
      ∀ w : Fin m → ℂ, (∀ h ∈ I, eval w h = 0) → eval w u ≠ 0 → eval w r = 0 → eval w g = 0 := by
    intro g hg
    have hg' : algebraMap _ (locRing I t) g ∈ Ideal.span {algebraMap _ (locRing I t) r} := hg
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hg'
    obtain ⟨c, b, hb, hcb⟩ := exists_mk_locRing I t a
    have h0 : algebraMap _ (locRing I t) (b * g - c * r) = 0 := by
      rw [map_sub, map_mul, map_mul, ← ha, ← hcb]
      ring
    obtain ⟨s, hs, hsI⟩ := IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
    refine ⟨s * b, ?_, fun w hw hsb hr => ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hs hb
    · have h1 := hw _ hsI
      rw [map_mul] at hsb
      rw [map_mul, map_sub, map_mul, map_mul, hr, mul_zero, sub_zero, ← mul_assoc] at h1
      exact (mul_eq_zero.1 h1).resolve_left hsb
  obtain ⟨S, hS⟩ : (Par.chPrime I t r).FG := IsNoetherian.noetherian _
  have hSm : ∀ g ∈ S, g ∈ Par.chPrime I t r := fun g hg => hS ▸ Ideal.subset_span hg
  choose! u hu hu' using fun g (hg : g ∈ S) => hgen g (hSm g hg)
  refine ⟨∏ g ∈ S, u g, ?_, fun w hw hs hr g hg => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 hu
  · rw [map_prod] at hs
    have hle : Par.chPrime I t r ≤ RingHom.ker (eval w) := by
      rw [← hS, Ideal.span_le]
      intro f hf
      exact hu' f hf w hw (Finset.prod_ne_zero_iff.1 hs f hf) hr
    exact hle hg
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp
