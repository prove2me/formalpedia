-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.Bdd.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:54.357262+00:00
-- url     : https://prove2.me/submissions/faaae493-9689-4da5-89d0-7e7a9f021803

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
theorem _root_.solution {t : ℤ} {x : F} (hx : Bdd F t x) : Bdd F t (-x) := by
  rwa [Bdd, Valuation.map_neg]
end Bdd
end GroundTheory.Automorphic.Spherical
