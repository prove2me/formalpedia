-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.le_of_bdd_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:29.596033+00:00
-- url     : https://prove2.me/submissions/e82e3f5d-9e29-4e97-86b1-3c1c4270e9d2

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
theorem _root_.solution {s t : ℤ} (h : Bdd F t ((uniformizer F : F) ^ s)) : t ≤ s := by
  rwa [Bdd, map_zpow₀, zpow_le_zpow_iff_right_of_lt_one₀ valuation_uniformizer_pos
    (valuation_uniformizer_lt_one F)] at h
end GroundTheory.Automorphic.Spherical
