-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.Bdd.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:55:24.075077+00:00
-- url     : https://prove2.me/submissions/4e6199da-0199-462b-bab6-e8b31afbe16a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Theorems.Thm_GroundTheory_Automorphic_Spherical_valuation_uniformizer_pos

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
theorem _root_.solution {s t : ℤ} {x : F} (hx : Bdd F t x) (h : s ≤ t) : Bdd F s x :=
  hx.trans (zpow_le_zpow_right_of_le_one₀ valuation_uniformizer_pos
    (valuation_uniformizer_lt_one F).le h)
end Bdd
end GroundTheory.Automorphic.Spherical
