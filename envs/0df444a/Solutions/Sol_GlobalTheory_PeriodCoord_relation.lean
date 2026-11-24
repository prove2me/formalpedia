-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:38:48.135897+00:00
-- url     : https://prove2.me/submissions/e7e7c06a-f678-4a87-b734-c0833716f76f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_PeriodCoord_imForm_apply
import Theorems.Thm_GlobalTheory_PeriodCoord_eq_zero_of_imForm
import Theorems.Thm_GlobalTheory_PeriodCoord_ext_period

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodCoord
noncomputable section
variable {g : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodCoord
theorem _root_.solution {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ty P₀) (hP : IsPeriod D ty P) (c : D.La →₀ ℝ)
    (hc : Finsupp.linearCombination ℝ P₀ c = 0) : Finsupp.linearCombination ℝ P c = 0 := by
  obtain ⟨M₀, -, -, h₀⟩ := hP₀.2.2.2.2
  obtain ⟨M, -, hpos, h⟩ := hP.2.2.2.2
  refine eq_zero_of_imForm hpos (ext_period hP fun y => ?_)
  have := congrArg (fun u => imForm M₀ u (P₀ y)) hc
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, imForm_apply, h, h₀, map_zero, LinearMap.zero_apply] at this ⊢
  exact this
end GlobalTheory.PeriodCoord
