-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isIso_of_isBasisOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:34.229868+00:00
-- url     : https://prove2.me/submissions/f5a9edf7-f55e-4047-b45a-10aa76ef2730

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isIso_of_locally_bijective
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bijective_app_of_isBasisOn

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
theorem _root_.solution {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (s : ((preMod X).obj M).obj (op U)),
      IsBasisOn ((preMod X).obj M) U s ∧ IsBasisOn ((preMod X).obj N) U (((preMod X).map f).app _ s)) :
    IsIso f := by
  apply isIso_of_locally_bijective
  intro x
  obtain ⟨U, hx, s, hs, hfs⟩ := hf x
  exact ⟨U, hx, fun V h => bijective_app_of_isBasisOn f hs hfs V h⟩
end GroundTheory.Arith.SchemeCoh
