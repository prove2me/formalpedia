-- Prove2me | solution 1 for GlobalTheory.EffCartierData.poleSecs_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:42:25.866912+00:00
-- url     : https://prove2.me/submissions/f21f99bf-4043-4b2e-b3d5-e2be1a783b72

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
variable [IsIntegral X]
namespace GlobalTheory.EffCartierData
theorem _root_.solution (V : X.Opens) [Nonempty V] : Monotone fun n => D.poleSecs n V := by
  refine monotone_nat_of_le_succ fun n h hh => ?_
  rw [mem_poleSecs_iff_stalk] at hh ⊢
  intro i x hx hi
  obtain ⟨r, hr⟩ := hh i x hx hi
  exact ⟨(X.presheaf.germ _ x hi).hom (D.f i) * r, by rw [map_mul, hr]; ring⟩
end GlobalTheory.EffCartierData
