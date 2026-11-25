-- Prove2me | solution 1 for GlobalTheory.EffCartierData.idealSheaf_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:14.208828+00:00
-- url     : https://prove2.me/submissions/b45c51ab-44dc-4a4c-b3f8-002e0b71311a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_eq_idealSheaf

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
namespace GlobalTheory.EffCartierData
theorem _root_.solution (n : ℕ) : (D.nsmul n).idealSheaf = D.idealSheaf ^ n := by
  refine ((D.nsmul n).eq_idealSheaf fun x => ?_).symm
  obtain ⟨i, hi⟩ := D.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le hi
  refine ⟨W, i, hW, hxW, ?_⟩
  change D.idealSheaf.ideal W ^ n = _
  rw [D.ideal_idealSheaf W i hW, Ideal.span_singleton_pow, ← map_pow]
  rfl
end GlobalTheory.EffCartierData
