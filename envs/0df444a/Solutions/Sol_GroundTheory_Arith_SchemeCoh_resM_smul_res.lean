-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.resM_smul_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:03.002895+00:00
-- url     : https://prove2.me/submissions/805e6b56-9153-4c5f-8759-3278547ad4ea

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_resM
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_smul

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
theorem _root_.solution (P : PMod X) {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (r : ringOn X V)
    (x : P.obj (op U)) : resM P i (r • resM P h x) = resR i r • resM P (i.trans h) x := by
  rw [resM_smul, resM_resM]
end GroundTheory.Arith.SchemeCoh
