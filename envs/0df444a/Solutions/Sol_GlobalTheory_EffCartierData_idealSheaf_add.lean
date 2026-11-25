-- Prove2me | solution 1 for GlobalTheory.EffCartierData.idealSheaf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:43:25.715868+00:00
-- url     : https://prove2.me/submissions/47ffd25e-39b0-47bd-a88e-7021216dfe2e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_eq_idealSheaf
import Theorems.Thm_GlobalTheory_EffCartierData_resG_add_f

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
theorem _root_.solution : (D.add D').idealSheaf = D.idealSheaf * D'.idealSheaf := by
  refine ((D.add D').eq_idealSheaf fun x => ?_).symm
  obtain ⟨i, hi⟩ := D.exists_mem x
  obtain ⟨j, hj⟩ := D'.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := D.U i ⊓ D'.U j) ⟨hi, hj⟩
  refine ⟨W, (i, j), hW, hxW, ?_⟩
  change D.idealSheaf.ideal W * D'.idealSheaf.ideal W = _
  rw [D.ideal_idealSheaf W i (hW.trans inf_le_left), D'.ideal_idealSheaf W j (hW.trans inf_le_right),
    Ideal.span_singleton_mul_span_singleton]
  exact congrArg (fun a => Ideal.span {a}) (D.resG_add_f D' i j hW).symm
end GlobalTheory.EffCartierData
