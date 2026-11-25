-- Prove2me | solution 1 for GlobalTheory.Cube.d_termDirectSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:38:44.609215+00:00
-- url     : https://prove2.me/submissions/80bdf62e-b142-4b92-89c4-14c9477ea388

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
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : κ → Cube.{v} ι R) (p : ℕ) (x : ⨁ k, Cube.Term (A k) p) :
    Cube.d (Cube.directSum A) p (Cube.termDirectSum A p x) =
      Cube.termDirectSum A (p + 1) (DirectSum.lmap (fun k => Cube.d (A k) p) x) := by
  have : Cube.d (Cube.directSum A) p ∘ₗ Cube.termDirectSum A p =
      Cube.termDirectSum A (p + 1) ∘ₗ DirectSum.lmap (fun k => Cube.d (A k) p) := by
    refine DirectSum.linearMap_ext _ fun k => LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Cube.termDirectSum_lof, DirectSum.lmap_lof, Cube.termMap_d]
  exact congr($this x)
end Cube
end GlobalTheory
