-- Prove2me | solution 1 for GlobalTheory.UnifZero.secScal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:48:59.068426+00:00
-- url     : https://prove2.me/submissions/a99eb3cc-2647-440d-9107-a0f0986402ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Theorems.Thm_GlobalTheory_UnifZero_resTop_inj
import Theorems.Thm_GlobalTheory_UnifZero_resTop_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable {X Y Y' : Scheme.{0}} {J J' J'' : Type} [Fintype J] [Fintype J'] [Fintype J'']
namespace GlobalTheory.UnifZero
theorem _root_.solution {φ₁ : J → (Y' ⟶ X)} {ε₁ : J → ℤ} {s₁ : LB.Sec (LB.LinComb (trivLB X) φ₁ ε₁)}
    {φ₂ : J' → (Y ⟶ X)} {ε₂ : J' → ℤ} {s₂ : LB.Sec (LB.LinComb (trivLB X) φ₂ ε₂)} {a : Γ(Y', ⊤)}
    {b : Γ(Y, ⊤)} (ha : SecConst s₁ a) (hb : SecConst s₂ b) (h : Y' ⟶ Y) (c : Γ(Y', ⊤)) :
    GeneratorPullback.SecScal (trivLB X) φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c ↔ h.appTop.hom b = c * a := by
  constructor
  · intro H
    have := H (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ _ _ => rfl)
    erw [ha, hb, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, ← resTop_mul] at this
    exact resTop_inj (top_unique (le_inf (wchart_triv _ _).ge (wchart_triv _ _).ge)) this
  · intro H j₁ j₂ _
    erw [ha, hb, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, ← resTop_mul, H]
end GlobalTheory.UnifZero
