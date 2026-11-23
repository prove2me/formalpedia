-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.exists_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:07.056996+00:00
-- url     : https://prove2.me/submissions/5ac0f751-409d-4833-a1e5-ebe17a23825b

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
variable {A : ι → Type} [∀ i, CommRing (A i)] {B : Type} [CommRing B]
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {Q : ∀ i, (B →+* A i) → Prop}
    (H : ∀ᶠ i in (U : Filter ι), ∃ p : B →+* A i, Q i p) :
    ∃ h : ∀ i, B → A i, ∀ᶠ i in (U : Filter ι), ∃ p : B →+* A i, ⇑p = h i ∧ Q i p := by
  classical
  refine ⟨fun i => if hx : ∃ p : B →+* A i, Q i p then ⇑hx.choose else 0, ?_⟩
  filter_upwards [H] with i hi
  exact ⟨hi.choose, by simp [dif_pos hi], hi.choose_spec⟩
end GlobalTheory.CompanionTheory.Ultra
