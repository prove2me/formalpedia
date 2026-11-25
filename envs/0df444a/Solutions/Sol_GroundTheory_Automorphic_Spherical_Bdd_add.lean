-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.Bdd.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:51.883465+00:00
-- url     : https://prove2.me/submissions/388348cf-4ef5-4aaf-a95b-9119afaa1146

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
namespace Bdd
theorem _root_.solution {t : ℤ} {x y : F} (hx : Bdd F t x) (hy : Bdd F t y) : Bdd F t (x + y) :=
  (Valuation.map_add _ x y).trans (max_le hx hy)
end Bdd
end GroundTheory.Automorphic.Spherical
