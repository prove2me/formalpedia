-- Prove2me | solution 1 for GroundTheory.Arith.Etale.pullbackSection_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:45.295484+00:00
-- url     : https://prove2.me/submissions/06cc9fda-8dd9-44aa-9bcd-81e576e19c56

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
variable {T U W : Scheme.{u}}
namespace GroundTheory.Arith.Etale
theorem _root_.solution (g : T ⟶ U) (N : U.Modules) (a : Γ(U, ⊤)) (n : Γ(N, ⊤)) :
    pullbackSection g N (a • n) = g.appTop a • pullbackSection g N n :=
  Scheme.Modules.Hom.app_smul _ a n
end GroundTheory.Arith.Etale
