-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig.renR_sub_deh_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:12:08.558863+00:00
-- url     : https://prove2.me/submissions/8ff89502-a3a7-49b0-a64d-b92c5641de86

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturatedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRingAltBis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartRegularAtConePoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Sig_renR_X_sub_one_mem

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
theorem _root_.solution (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    renR (Σ k, ι k) f - bind₁ (SncRes.lift p) f ∈ SncRes.ideal S p := by
  classical
  have key : (Ideal.Quotient.mk (SncRes.ideal S p)).comp
        (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) =
      (Ideal.Quotient.mk (SncRes.ideal S p)).comp
        (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [renameEquiv_apply]
    · rintro ⟨k, i⟩
      by_cases h : i = p k
      · subst h
        have h1 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
        have h2 := renR_X_sub_one_mem S p k
        rw [map_sub, map_one] at h2
        simpa [h1] using Ideal.Quotient.eq.2 h2
      · have h1 : SncRes.lift p ⟨k, i⟩ = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
          simp [SncRes.lift, h]
        simp [h1, renameEquiv_apply]
  exact Ideal.Quotient.eq.1 (RingHom.congr_fun key f)
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
