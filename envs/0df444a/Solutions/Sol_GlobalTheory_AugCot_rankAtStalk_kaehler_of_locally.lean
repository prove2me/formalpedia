-- Prove2me | solution 1 for GlobalTheory.AugCot.rankAtStalk_kaehler_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:29:57.265277+00:00
-- url     : https://prove2.me/submissions/1bdabf2d-ac04-4925-a0ee-150d87a3e0dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_finrank_kaehler_of_isStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_smooth_of_locally

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) {n : ℕ}
namespace GlobalTheory.AugCot
theorem _root_.solution
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (q : PrimeSpectrum A) : Module.rankAtStalk Ω[A⁄R] q = n := by
  haveI := smooth_of_locally h
  obtain ⟨s, hs, H⟩ := h
  obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ q.asIdeal := by
    by_contra! hc
    exact q.2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away t) t]
    exact htq
  obtain ⟨q', rfl⟩ := hq
  have Ht := H t hts
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at Ht
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := R)
    (S := Localization.Away t)
  haveI : Nontrivial (Localization.Away t) := q'.nontrivial
  haveI := Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.Away t) (Submonoid.powers t)
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A (Localization.Away t)),
    Module.rankAtStalk_eq_finrank_of_free,
    finrank_kaehler_of_isStandardSmoothOfRelativeDimension n]
  rfl
end GlobalTheory.AugCot
