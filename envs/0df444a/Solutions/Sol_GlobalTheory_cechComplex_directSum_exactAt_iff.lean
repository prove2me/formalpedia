-- Prove2me | solution 1 for GlobalTheory.cechComplex_directSum_exactAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:10.761385+00:00
-- url     : https://prove2.me/submissions/06bd8034-9c84-4ec7-a2de-f0e58dbcf6a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
open DirectSum
variable {R : Type u} [Ring R] {κ : Type} [DecidableEq κ]
variable {ι : Type}
variable [LinearOrder ι]
variable [Finite ι]
omit [DecidableEq κ]
namespace GlobalTheory
theorem _root_.solution (A : κ → Cube.{v} ι R) (p : ℕ) :
    (cechComplex (Cube.directSum A)).ExactAt p ↔ ∀ k, (cechComplex (A k)).ExactAt p := by
  classical
  simp only [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  rw [← (cechHomologyDirectSumEquiv A p).toEquiv.subsingleton_congr]
  exact ⟨fun _ k => (DirectSum.of_injective (β := fun k => (cechComplex (A k)).homology p)
    k).subsingleton, fun _ => ⟨fun _ _ => DFinsupp.ext fun _ => Subsingleton.elim _ _⟩⟩
end GlobalTheory
