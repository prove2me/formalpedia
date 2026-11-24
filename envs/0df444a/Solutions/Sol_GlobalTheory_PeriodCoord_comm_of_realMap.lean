-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.comm_of_realMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:32.166552+00:00
-- url     : https://prove2.me/submissions/64bfae08-0c27-447d-9c19-254ed9b50995

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_PeriodCoord_realMap_apply
import Theorems.Thm_GlobalTheory_PeriodCoord_realMap_inj
import Theorems.Thm_GlobalTheory_PeriodCoord_ext_period
import Theorems.Thm_GlobalTheory_PeriodCoord_period_smul
import Theorems.Thm_GlobalTheory_PeriodCoord_star_actMat

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
theorem _root_.solution {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ty P₀) (hP : IsPeriod D ty P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (a : 𝓞 E) :
    actMat ty a * A = A * actMat ty a ∧ actMat ty a * B = B * actMat ty (H.bar a) := by
  refine realMap_inj (ext_period hP₀ fun x => ?_)
  have := h (a • x)
  rw [period_smul hP, period_smul hP₀, h] at this
  simp only [realMap_apply, star_actMat (H := H), mulVec_add, mulVec_mulVec] at this ⊢
  exact this
end GlobalTheory.PeriodCoord
