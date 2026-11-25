-- Prove2me | solution 1 for GlobalTheory.T.alternating_product_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:13.485721+00:00
-- url     : https://prove2.me/submissions/555d6d56-4a89-406f-9054-901ffd8a4d29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingProductIntegral
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductIntegral
import Theorems.Thm_GlobalTheory_DI_alt_mem_forms


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι), (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s → ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  first | exact @_root_.GlobalTheory.DI.alt_mem_forms | exact _root_.GlobalTheory.DI.alt_mem_forms | (intros; apply _root_.GlobalTheory.DI.alt_mem_forms <;> assumption)
end _root_.GlobalTheory.T
