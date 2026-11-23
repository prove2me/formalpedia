-- Prove2me | solution 1 for GlobalTheory.FrameValue.genVal_corr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:50.157804+00:00
-- url     : https://prove2.me/submissions/e1a7e089-59a3-42db-8b3d-18c1e14a5f75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_le_chartAt
import Theorems.Thm_GlobalTheory_FrameValue_le_wchart_chartAt
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_res
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ}
variable {u}
namespace GlobalTheory.FrameValue
theorem _root_.solution (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ}
    (hz : IsLift u φ y z) (hz' : IsLift u φ' y z')
    (hs : ∀ f : (Fin g → ℂ) → ℂˣ, ∏ k, f (z k) ^ ε k = ∏ k, f (z' k) ^ ε' k) :
    genVal u hL t y z = genVal u hL t' y z' := by
  have h₁ := le_wchart_chartAt hL φ y
  have h₂ := le_wchart_chartAt hL φ' y
  have h₃ := (le_preimage_inf y _ _).2 ⟨h₁, h₂⟩
  refine congrArg₂ (· / ·) ?_ ?_
  · refine (val_res y valueRules inf_le_left h₃ _).symm.trans (Eq.trans ?_ (val_res y valueRules inf_le_right h₃ _))
    exact congrArg (fun q : Γ(Y, _)ˣ => valAt' y _ q.val) (h _ _ (fun a b e => congrArg (fun q => chartAt hL (y ≫ q)) e)
      (fun a b e => congrArg (fun q => chartAt hL (y ≫ q)) e) (fun a b e => congrArg (fun q => chartAt hL (y ≫ q)) e))
  · have := congrArg (Units.coeHom ℂ) (hs fun w => Units.mk0 _ (u.fr_ne _ w (le_chartAt hL (u.ex w).left)))
    simp only [map_prod, map_zpow, Units.coeHom_apply, Units.val_mk0] at this
    simp only [frameProd, hz _, hz' _]
    exact this
end GlobalTheory.FrameValue
