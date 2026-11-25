-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.Bdd.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:37.518294+00:00
-- url     : https://prove2.me/submissions/af942c67-425d-42cf-9dbf-d7b444d4e947

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
theorem _root_.solution {s t : ℤ} {x y : F} (hx : Bdd F s x) (hy : Bdd F t y) : Bdd F (s + t) (x * y) := by
  rw [Bdd, map_mul, zpow_add₀ (valuation_uniformizer_ne_zero F)]
  exact mul_le_mul' hx hy
end Bdd
end GroundTheory.Automorphic.Spherical
