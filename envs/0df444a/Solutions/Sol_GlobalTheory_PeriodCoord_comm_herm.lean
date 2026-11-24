-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.comm_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:22:50.749685+00:00
-- url     : https://prove2.me/submissions/15c600a3-7022-4c11-8081-84b4106c2c09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_PeriodCoord_imForm_apply
import Theorems.Thm_GlobalTheory_PeriodCoord_realMap_apply
import Theorems.Thm_GlobalTheory_PeriodCoord_ext_period
import Theorems.Thm_GlobalTheory_PeriodCoord_period_smul

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
theorem _root_.solution {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ty P₀) {M : Matrix (Fin g) (Fin g) ℂ}
    (hM : ∀ x y, (hermForm M (P₀ x) (P₀ y)).im = D.EF x y) (a : 𝓞 E) :
    actMat ty a * M = M * actMat ty a := by
  have key : (imForm M).compl₁₂ (realMap (actMat ty a) 0) LinearMap.id =
      (imForm M).compl₁₂ LinearMap.id (realMap (actMat ty (H.bar a)) 0) := by
    refine ext_period hP₀ fun x => ext_period hP₀ fun y => ?_
    simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
      ← period_smul hP₀, imForm_apply, hM, D.adj]
  ext i j
  have h1 := LinearMap.congr_fun₂ key (Pi.single i 1) (Pi.single j 1)
  have h2 := LinearMap.congr_fun₂ key (Pi.single i Complex.I) (Pi.single j 1)
  simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
    imForm_apply, actMat, diagonal_mulVec_single, hermForm, ← Pi.single_star, H.bar_eq,
    IsCMField.complexEmbedding_complexConj] at h1 h2
  simp only [actMat, diagonal_mul, mul_diagonal]
  simp at h1 h2
  apply Complex.ext <;> simp <;> linarith
end GlobalTheory.PeriodCoord
