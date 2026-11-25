-- Prove2me | solution 1 for GlobalTheory.EffCartierData.idealSheaf_eq_of_secMaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:53.722818+00:00
-- url     : https://prove2.me/submissions/88efdab2-cddd-44ac-bbd0-c2f0dd649f99

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_eq_idealSheaf
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_on


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
theorem _root_.solution {w : LB.Iso D.lb D'.lb}
    (hw : SecMaps w D.canonical D'.canonical) : D.idealSheaf = D'.idealSheaf := by
  refine D'.eq_idealSheaf fun x => ?_
  obtain ⟨q, hq⟩ := D.exists_mem x
  obtain ⟨p, hp⟩ := D'.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := D'.U p ⊓ D.U q) ⟨hp, hq⟩
  refine ⟨W, p, hW.trans inf_le_left, hxW, ?_⟩
  rw [D.ideal_idealSheaf W q (hW.trans inf_le_right)]
  exact (Ideal.span_singleton_mul_left_unit ((Units.isUnit _).map _) _).symm.trans
    (congrArg (fun a => Ideal.span {a})
      (hw.on p q (hW.trans inf_le_left) (hW.trans inf_le_right)).symm)
end GlobalTheory.EffCartierData
