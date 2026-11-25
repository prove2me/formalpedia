-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.bijective_app_of_isBasisOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:10.147697+00:00
-- url     : https://prove2.me/submissions/252f4ae9-d9d8-40d7-bc4b-6f0d3e4a1080

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_resM
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {M N : X.Modules} (f : M ⟶ N) {U : X.Opens}
    {s : ((preMod X).obj M).obj (op U)} (hs : IsBasisOn ((preMod X).obj M) U s)
    (hfs : IsBasisOn ((preMod X).obj N) U (((preMod X).map f).app _ s)) (V : X.Opens) (h : V ≤ U) :
    Function.Bijective (f.app V) := by
  have e : (fun r : ringOn X V => r • resM ((preMod X).obj N) h (((preMod X).map f).app _ s)) =
      f.app V ∘ (fun r : ringOn X V => r • resM ((preMod X).obj M) h s) := by
    funext r
    change _ = ((preMod X).map f).app (op V) (r • resM ((preMod X).obj M) h s)
    rw [app_smul, app_resM]
  have h1 := hfs V h
  rw [e] at h1
  exact (Function.Bijective.of_comp_iff _ (hs V h)).1 h1
end GroundTheory.Arith.SchemeCoh
