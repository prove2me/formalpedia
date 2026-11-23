-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.exists_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:10.391334+00:00
-- url     : https://prove2.me/submissions/724cf428-68a8-4a3f-9e9a-f964b62eee4c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {α : Type} {S : Set α} (hS : S.Finite) {Q : α → ι → Prop}
    (H : ∀ᶠ i in (U : Filter ι), ∃ W ∈ S, Q W i) : ∃ W ∈ S, ∀ᶠ i in (U : Filter ι), Q W i := by
  by_contra hcon
  push_neg at hcon
  have : ∀ᶠ i in (U : Filter ι), ∀ W ∈ S, ¬ Q W i :=
    (Filter.eventually_all_finite hS).2 fun W hW => hcon W hW
  obtain ⟨i, ⟨W, hW, h1⟩, h2⟩ := (H.and this).exists
  exact h2 W hW h1
end GlobalTheory.CompanionTheory.Ultra
