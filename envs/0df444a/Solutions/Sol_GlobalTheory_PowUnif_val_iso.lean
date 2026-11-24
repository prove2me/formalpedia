-- Prove2me | solution 1 for GlobalTheory.PowUnif.val_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:03.48509+00:00
-- url     : https://prove2.me/submissions/0e2f90fb-9a66-411c-94b4-514ce2404f56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_val_gen
import Theorems.Thm_GlobalTheory_PowUnif_val_div_g
import Theorems.Thm_GlobalTheory_PowUnif_val_linComb_g
import Theorems.Thm_GlobalTheory_top_le_preimage_inf


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
variable {X Y : Scheme.{0}}
namespace GlobalTheory.PowUnif
theorem _root_.solution (x : Sp ℂ ⟶ Y) (L : LB X) (L' : LB Y) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (w : LB.Iso L' (LB.LinComb L φ (fun _ => 1))) (hw : w.IsGen) (jj jj' : K → L.ι) (b b' : L'.ι)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ jj) (h₂ : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ jj')
    (h₃ : ⊤ ≤ x ⁻¹ᵁ L'.U b) (h₄ : ⊤ ≤ x ⁻¹ᵁ L'.U b') :
    valAt' x (LB.wchart L φ jj ⊓ L'.U b) (w.s (jj, b)).val =
      (∏ k, valAt' (x ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val) *
        (valAt' x (L'.U b ⊓ L'.U b') (L'.g b b').val)⁻¹ *
        valAt' x (LB.wchart L φ jj' ⊓ L'.U b') (w.s (jj', b')).val := by
  have hV : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ jj ⊓ L'.U b ⊓ (LB.wchart L φ jj' ⊓ L'.U b')) := by
    simp only [top_le_preimage_inf]; exact ⟨⟨h₁, h₃⟩, h₂, h₄⟩
  have h12 : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ jj ⊓ LB.wchart L φ jj') := (top_le_preimage_inf _ _ _).2 ⟨h₁, h₂⟩
  rw [← val_linComb_g x L φ jj jj' h12]
  exact (val_gen hw x (jj, b) (jj', b') hV).trans
    (congrArg (· * _) (val_div_g (LB.LinComb L φ (fun _ => 1)) L' x jj jj' b b' hV))
end GlobalTheory.PowUnif
