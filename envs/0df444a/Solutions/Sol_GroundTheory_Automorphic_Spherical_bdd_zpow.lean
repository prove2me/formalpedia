-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.bdd_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:45:27.663804+00:00
-- url     : https://prove2.me/submissions/ec66e42c-ad76-44c9-83f8-dbf8553f7d0c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (t : ℤ) : Bdd F t ((uniformizer F : F) ^ t) := by
  rw [Bdd, map_zpow₀]
end GroundTheory.Automorphic.Spherical
