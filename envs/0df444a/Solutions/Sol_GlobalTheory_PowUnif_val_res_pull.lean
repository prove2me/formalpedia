-- Prove2me | solution 1 for GlobalTheory.PowUnif.val_res_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:58.138411+00:00
-- url     : https://prove2.me/submissions/63546716-0667-4255-adf4-d56f5c0bba12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_val_res
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a


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
theorem _root_.solution (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) {V : X.Opens} (h : V ≤ φ ⁻¹ᵁ U) (s : Γ(Y, U)ˣ)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V (res h (pullU φ U s)).val = valAt' (x ≫ φ) U s.val :=
  (val_res x h _ hV).trans (valAt'_comp x φ U s.val)
end GlobalTheory.PowUnif
