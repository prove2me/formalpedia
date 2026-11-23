-- Prove2me | solution 1 for GlobalTheory.cubeComplex_directSum_exactAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:24.450903+00:00
-- url     : https://prove2.me/submissions/1364d324-17d3-4ed5-9d84-f46bf2093684

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
    (cubeComplex (Cube.directSum A)).ExactAt p ↔ ∀ k, (cubeComplex (A k)).ExactAt p := by
  classical
  simp only [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  rw [← (cubeHomologyDirectSumEquiv A p).toEquiv.subsingleton_congr]
  exact ⟨fun _ k => (DirectSum.of_injective (β := fun k => (cubeComplex (A k)).homology p)
    k).subsingleton, fun _ => ⟨fun _ _ => DFinsupp.ext fun _ => Subsingleton.elim _ _⟩⟩
end GlobalTheory
