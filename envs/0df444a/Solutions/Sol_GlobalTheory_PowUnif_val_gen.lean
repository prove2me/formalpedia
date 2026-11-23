-- Prove2me | solution 1 for GlobalTheory.PowUnif.val_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:14.802516+00:00
-- url     : https://prove2.me/submissions/efc8d3c2-72a0-4a65-b2db-06c6a170cc86

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
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2


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
theorem _root_.solution {L : LB X} {t : L.Gen} (ht : t.IsGen) (x : Sp ℂ ⟶ X) (i k : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    valAt' x (L.U i) (t.s i).val = valAt' x (L.U i ⊓ L.U k) (L.g i k).val * valAt' x (L.U k) (t.s k).val := by
  rw [← val_res x (inf_le_left : L.U i ⊓ L.U k ≤ _) _ h, ht i k, Units.val_mul, valAt'_mul, val_res x _ _ h]
end GlobalTheory.PowUnif
