-- Prove2me | solution 1 for GlobalTheory.QNorm.places_over
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:37.139856+00:00
-- url     : https://prove2.me/submissions/d731624f-e9fa-4a26-a6c0-13f59b6d066d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Theorems.Thm_GlobalTheory_QNorm_finite_places_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ SE : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), ∃ e : ℕ, 0 < e ∧ ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x ^ e := by
  intro F E _ _ _ _ _
  refine ⟨fun S => ?_, fun v => ?_, fun w => ?_⟩
  · have hfin : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S}.Finite := by
      have hU : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S} =
          ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v} := by
        ext w; simp
      rw [hU]
      exact S.finite_toSet.biUnion fun v _ => _root_.GlobalTheory.QNorm.finite_places_over F E v
    exact ⟨hfin.toFinset, fun w => by simp⟩
  · obtain ⟨P, hmax, hover⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.asIdeal (S := 𝓞 E)
    have hne : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
    exact ⟨⟨P, hmax.isPrime, hne⟩, HeightOneSpectrum.ext hover.over.symm⟩
  · haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    refine ⟨(w.under (𝓞 F)).asIdeal.ramificationIdx' w.asIdeal, Nat.pos_of_ne_zero ?_,
      fun x => ?_⟩
    · refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero ?_ w.isPrime Ideal.map_comap_le
      rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
      exact (w.under (𝓞 F)).ne_bot
    · exact (HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 F)) w x).symm
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
