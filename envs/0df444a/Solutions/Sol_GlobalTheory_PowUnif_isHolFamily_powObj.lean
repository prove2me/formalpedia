-- Prove2me | solution 1 for GlobalTheory.PowUnif.isHolFamily_powObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:52:07.92483+00:00
-- url     : https://prove2.me/submissions/ef9a417c-c955-4bb0-8397-d4374ac3c17b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_isHolFamily_const
import Theorems.Thm_GlobalTheory_PowUnif_isHolFamily_tensor

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
theorem _root_.solution (G : Over (Sp ℂ)) : ∀ (n : ℕ) (c : E → (𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj G n)),
    (∀ i, IsHolFamily (Z := G.left) (fun z => (c z ≫ Out.powPr G i).left)) →
    IsHolFamily (Z := (Out.powObj G n).left) (fun z => (c z).left)
  | 0, c, _ => by
    have : c = fun _ => 𝟙 _ := funext fun z => toUnit_unique _ _
    subst this
    exact isHolFamily_const _
  | n + 1, c, h => by
    refine isHolFamily_tensor G (Out.powObj G n) c (h 0) (solution G n (fun z => c z ≫ snd _ _) fun i => ?_)
    have h1 : (fun z => ((c z ≫ snd G (Out.powObj G n)) ≫ Out.powPr G i).left) =
        fun z => (c z ≫ Out.powPr G i.succ).left := funext fun z => congrArg _ (Category.assoc _ _ _)
    exact h1 ▸ h i.succ
end GlobalTheory.PowUnif
