-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.valuation_uniformizer_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:08.973796+00:00
-- url     : https://prove2.me/submissions/71f53ec7-e5c6-4887-97ea-a4e8fa3b8049

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
theorem _root_.solution : 0 < valuation F (uniformizer F : F) :=
  zero_lt_iff.2 (valuation_uniformizer_ne_zero F)
end GroundTheory.Automorphic.Spherical
