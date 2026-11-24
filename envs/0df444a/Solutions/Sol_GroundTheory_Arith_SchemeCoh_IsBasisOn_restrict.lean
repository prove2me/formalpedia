-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsBasisOn.restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:46.312342+00:00
-- url     : https://prove2.me/submissions/a869dae7-ee3d-4f08-a99e-bb547d6ea8a5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorToSheaf_tensorLift
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_resM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GroundTheory.Arith.SchemeCoh.tensorToSheaf_tensorLift

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
namespace IsBasisOn
theorem _root_.solution {P : PMod X} {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    {V : X.Opens} (h : V ≤ U) : IsBasisOn P V (resM P h s) := by
  intro W i
  have := hs W (i.trans h)
  simp only [resM_resM]
  exact this
end IsBasisOn
end GroundTheory.Arith.SchemeCoh
