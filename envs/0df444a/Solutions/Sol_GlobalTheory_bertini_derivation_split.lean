-- Prove2me | solution 1 for GlobalTheory.bertini_derivation_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:18.051119+00:00
-- url     : https://prove2.me/submissions/8eaac67d-4462-4e16-833a-6c2e19501045

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationSplitKaehlerDSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KaehlerDifferential
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A], ∃ (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l := by
  intro k A _ _ _ _
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A (KaehlerDifferential k A)
  refine ⟨n, fun l => (LinearMap.proj l ∘ₗ g).compDer (KaehlerDifferential.D k A), fun l => f (Pi.single l 1), ?_⟩
  intro a
  have h := LinearMap.congr_fun hfg (KaehlerDifferential.D k A a)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_lhs => rw [← h]
  conv_lhs => rw [pi_eq_sum_univ (g (KaehlerDifferential.D k A a))]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]
end GlobalTheory
