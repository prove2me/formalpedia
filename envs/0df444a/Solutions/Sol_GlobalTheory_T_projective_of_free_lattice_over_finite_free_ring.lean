-- Prove2me | solution 1 for GlobalTheory.T.projective_of_free_lattice_over_finite_free_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:36.314086+00:00
-- url     : https://prove2.me/submissions/ed6ee8fe-6c19-41ca-9289-e7f04a52f143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProjectiveOfFreeLatticeOverFiniteFreeRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProjectiveOfFreeLatticeOverFiniteFreeRingStatement
import Theorems.Thm_GlobalTheory_projective_compHom_of_free_of_finite_free


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  first | exact @GlobalTheory.projective_compHom_of_free_of_finite_free | exact GlobalTheory.projective_compHom_of_free_of_finite_free | (intros; apply GlobalTheory.projective_compHom_of_free_of_finite_free <;> assumption)
end _root_.GlobalTheory.T
