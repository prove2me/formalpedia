-- Prove2me | solution 1 for GlobalTheory.PowUnif.val_linComb_g
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:40.633802+00:00
-- url     : https://prove2.me/submissions/c5cb9c8b-ef60-475f-a6a3-d4548dc57d3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_val_res_pull
import Theorems.Thm_P2M_GlobalTheory_valAt__units_prod_4b684ea369c1


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
theorem _root_.solution (x : Sp ℂ ⟶ Y) (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (jj jj' : K → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ jj ⊓ LB.wchart L φ jj')) :
    valAt' x (LB.wchart L φ jj ⊓ LB.wchart L φ jj') ((LB.LinComb L φ (fun _ => 1)).g jj jj').val =
      ∏ k, valAt' (x ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val := by
  refine (valAt'_units_prod x h Finset.univ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  rw [zpow_one]
  exact val_res_pull x (φ k) (L.U (jj k) ⊓ L.U (jj' k)) _ _ h
end GlobalTheory.PowUnif
