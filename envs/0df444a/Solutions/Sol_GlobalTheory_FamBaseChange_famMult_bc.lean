-- Prove2me | solution 1 for GlobalTheory.FamBaseChange.famMult_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:49.486418+00:00
-- url     : https://prove2.me/submissions/a1d8f7a1-dc35-4507-bc6c-9f8989579370

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralDegenerationFamilyBaseChangeExtensionFie
import Theorems.Thm_GlobalTheory_FamBaseChange_toGen_jFK
import Theorems.Thm_GlobalTheory_FamBaseChange_bc_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_val_famMult


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamBaseChange
theorem _root_.solution (k : ℕ) (α mu : D.X) (y : (DegPre.BF D F).left) {J} (hJ : Good D.P.L y J) :
    val (DegPre.famMult D (FractionRing R) k mu α) (bc D F ≫ fst _ _).left y J =
      val (DegPre.famMult D F k mu α) (𝟙 (DegPre.BF D F) ≫ fst _ _).left y J := by
  have e : (bc D F ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) =
      (𝟙 (DegPre.BF D F) ≫ fst _ _).left ≫ jFK (R := R) F := by
    rw [bc_fst, Category.id_comp, Over.comp_left, Category.assoc, toGen_jFK]
  rw [val_famMult _ hJ, val_famMult _ hJ, e]
end GlobalTheory.FamBaseChange
