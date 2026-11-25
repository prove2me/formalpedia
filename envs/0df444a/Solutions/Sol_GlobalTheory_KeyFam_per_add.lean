-- Prove2me | solution 1 for GlobalTheory.KeyFam.per_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:57.195945+00:00
-- url     : https://prove2.me/submissions/2824d0eb-fdd2-4d59-a5b2-dcbe7e2be8de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf

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
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyFam
open GlobalTheory.KeyPow
variable {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
namespace GlobalTheory.KeyFam
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g ⊕ Fin g → ℤ) :
    per τ (a + b) = per τ a + per τ b := by
  have h₁ : (fun i => (((a + b) (Sum.inl i) : ℤ) : ℂ)) =
      (fun i => (a (.inl i) : ℂ)) + fun i => (b (.inl i) : ℂ) := by
    funext i; simp
  have h₂ : (fun i => (((a + b) (Sum.inr i) : ℤ) : ℂ)) =
      (fun i => (a (.inr i) : ℂ)) + fun i => (b (.inr i) : ℂ) := by
    funext i; simp
  unfold per
  rw [h₁, h₂, Matrix.mulVec_add]
  abel
end GlobalTheory.KeyFam
