-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg.isRegularLocalRing_locRing_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:46:43.137806+00:00
-- url     : https://prove2.me/submissions/4f431c90-d75d-4275-88c6-50ad98ee2f55

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_IsRegularLocalRingLocRingOfSpan
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_le_ptIdeal_iff__72a6f546eb9f
import Theorems.Thm_ReciprocityTheory_AnForm_R_locRing_isLocalRing_isNoetherian
import Theorems.Thm_ReciprocityTheory_AnForm_R_maximalIdeal_locRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg
theorem _root_.solution :
    ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
      (r : Fin e → MvPolynomial (Fin m) ℂ), (∀ h ∈ I, eval t h = 0) →
      ringKrullDim (locRing I t) = e →
      Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
        Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) →
      IsRegularLocalRing (locRing I t) := by
  intro m e I t r hI hdim hspan
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian I t hI
  haveI := hloc
  haveI := hnoeth
  have hle : I ≤ ptIdeal t := (le_ptIdeal_iff' I t).2 hI
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [maximalIdeal_locRing hle, ← hspan, hdim]
  have h1 : (Set.range fun l => algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) (r l)).ncard ≤ e := by
    rw [← Set.image_univ]
    calc _ ≤ (Set.univ : Set (Fin e)).ncard := Set.ncard_image_le Set.finite_univ
      _ = e := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2 : (Ideal.span (Set.range fun l => algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) (r l))).spanFinrank ≤ e :=
    (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans h1
  exact_mod_cast h2
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg
