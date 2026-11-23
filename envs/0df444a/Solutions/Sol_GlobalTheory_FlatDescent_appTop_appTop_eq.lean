-- Prove2me | solution 1 for GlobalTheory.FlatDescent.appTop_appTop_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:58.074047+00:00
-- url     : https://prove2.me/submissions/078af94f-81ab-48a8-98e3-f34f60c6a69e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}
namespace GlobalTheory.FlatDescent
theorem _root_.solution {p : Y ⟶ X} {f g : Z ⟶ Y} (h : f ≫ p = g ≫ p) (a : Γ(X, ⊤)) :
    f.appTop (p.appTop a) = g.appTop (p.appTop a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, h]
end GlobalTheory.FlatDescent
