-- Prove2me | solution 1 for GlobalTheory.PrimeSection.res_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:09.308911+00:00
-- url     : https://prove2.me/submissions/97b79ee0-927f-4aa8-8c34-cfb566e1f12f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
namespace GlobalTheory.PrimeSection
theorem _root_.solution {X : Scheme.{u}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE h').op s) =
      X.presheaf.map (homOfLE (h.trans h')).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end GlobalTheory.PrimeSection
