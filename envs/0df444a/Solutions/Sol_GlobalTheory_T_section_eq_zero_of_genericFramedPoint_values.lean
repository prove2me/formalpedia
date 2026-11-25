-- Prove2me | solution 1 for GlobalTheory.T.section_eq_zero_of_genericFramedPoint_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:29.597799+00:00
-- url     : https://prove2.me/submissions/a4c151cf-18b1-4df6-adaa-677293db5739

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_SectionEqZeroOfGenericFramedPointValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_SectionEqZeroOfGenericFramedPointValuesStatement
import Theorems.Thm_GlobalTheory_Reg_sec_eq_zero_of_generic_values


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec Xo c a n, (∀ Z, evC h Z g = 0) → g = 0 := by
  first | exact @GlobalTheory.Reg.sec_eq_zero_of_generic_values | exact GlobalTheory.Reg.sec_eq_zero_of_generic_values | (intros; apply GlobalTheory.Reg.sec_eq_zero_of_generic_values <;> assumption)
end _root_.GlobalTheory.T
