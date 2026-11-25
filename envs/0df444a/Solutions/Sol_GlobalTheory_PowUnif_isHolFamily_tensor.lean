-- Prove2me | solution 1 for GlobalTheory.PowUnif.isHolFamily_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:17.45327+00:00
-- url     : https://prove2.me/submissions/a06e164a-bcd5-4280-aa9a-e8e6c86fbab8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_holFamily_lift
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.PowUnif
theorem _root_.solution (X Y : Over (Sp ℂ)) (c : E → (𝟙_ (Over (Sp ℂ)) ⟶ X ⊗ Y))
    (h0 : IsHolFamily (Z := X.left) (fun z => (c z ≫ fst _ _).left))
    (h1 : IsHolFamily (Z := Y.left) (fun z => (c z ≫ snd _ _).left)) :
    IsHolFamily (Z := (X ⊗ Y).left) (fun z => (c z).left) := by
  intro U f
  have := holFamily_lift valAt'_rules E Set.univ X Y (fun z => c z ≫ fst _ _)
    (fun z => c z ≫ snd _ _) (fun U f => by simpa only [Set.mem_univ, true_and] using h0 U f)
    (fun U f => by simpa only [Set.mem_univ, true_and] using h1 U f) U f
  simpa only [Set.mem_univ, true_and, ← comp_lift, lift_fst_snd, Category.comp_id] using this
end GlobalTheory.PowUnif
