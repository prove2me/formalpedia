-- Prove2me | solution 1 for GlobalTheory.T.exists_integralFlagChart_enlarge_containing_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:16:50.485599+00:00
-- url     : https://prove2.me/submissions/a4ce303d-c59e-4630-89bc-9896174e02ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralFlagChartEnlargeContainingValue
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralFlagChartEnlargeContainingValueStatement
import Theorems.Thm_GlobalTheory_Reg_Enlarge_enlarge_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (f : Rul Xo c) (P : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F)), (∀ e ∈ P.es, evR Xo c f P.yg ∈ P.R e) → IsIntegral (Algebra.adjoin c.F (P.gens : Set P.Ω)) (evR Xo c f P.yg) → ∃ P' : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F), evR Xo c f P'.yg ∈ Algebra.adjoin c.F (P'.gens : Set P'.Ω) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (algebraMap O c.F a) ∈ W) → ∀ y : FrPt Xo c L, P.Catches W y → P'.Catches W y := by
  first | exact @GlobalTheory.Reg.Enlarge.enlarge_exists | exact GlobalTheory.Reg.Enlarge.enlarge_exists | (intros; apply GlobalTheory.Reg.Enlarge.enlarge_exists <;> assumption)
end _root_.GlobalTheory.T
