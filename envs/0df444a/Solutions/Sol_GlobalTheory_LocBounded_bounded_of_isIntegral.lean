-- Prove2me | solution 1 for GlobalTheory.LocBounded.bounded_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:26:01.19962+00:00
-- url     : https://prove2.me/submissions/d008b29c-b415-4fe2-bb99-6c69533d1724

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
import Theorems.Thm_GlobalTheory_LocBounded_bounded_of_isIntegral_general

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded
namespace GlobalTheory.LocBounded
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (N : Matrix (Fin n) (Fin n) (w.adicCompletion E)), N.charpoly.Separable → ∃ c : WithZero (Multiplicative ℤ), ∀ g ∈ Algebra.adjoin (w.adicCompletion E) {N}, IsIntegral (w.adicCompletionIntegers E) g → ∀ i j, Valued.v (g i j) ≤ c := by
  intro E _ _ w n N hsep
  refine bounded_of_isIntegral_general (O := w.adicCompletionIntegers E) Valued.v
    (fun y => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2)
    (fun x hx => ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx⟩, rfl⟩)
    (fun x hx => ?_) N hsep
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2
end GlobalTheory.LocBounded
