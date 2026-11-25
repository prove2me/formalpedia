-- Prove2me | solution 1 for GlobalTheory.exists_pow_eq_span_singleton_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:33.280915+00:00
-- url     : https://prove2.me/submissions/00bf0dac-f1c9-4fd6-a1a6-b6aec83c2f15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFiniteExtensionCapitulationComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E : Type) [Field E] [NumberField E]
    (I : Submodule (𝓞 E) E) (hI : I.FG) :
    ∃ n : ℕ, ∃ β : E, I ^ (n + 1) = Submodule.span (𝓞 E) {β} := by
  classical
  by_cases h0 : I = ⊥
  · exact ⟨0, 0, by simp [h0]⟩
  let F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  have hF : F ≠ 0 := by
    intro h
    apply h0
    have := congrArg (fun G : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (G : Submodule (𝓞 E) E)) h
    simpa [F] using this
  let u := Units.mk0 F hF
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card (ClassGroup (𝓞 E)) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h1 : ClassGroup.mk E (u ^ (n + 1)) = 1 := by
    rw [map_pow, ← hn, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨β, hβ⟩ := h1
  refine ⟨n, β, ?_⟩
  rw [← hβ, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl
end GlobalTheory
