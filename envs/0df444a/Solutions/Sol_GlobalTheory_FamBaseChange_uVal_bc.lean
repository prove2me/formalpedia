-- Prove2me | solution 1 for GlobalTheory.FamBaseChange.uVal_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:40.703687+00:00
-- url     : https://prove2.me/submissions/781dad9a-67fc-4da2-8ee7-addea76160d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralDegenerationFamilyBaseChangeExtensionFie
import Theorems.Thm_GlobalTheory_FamBaseChange_bc_prB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP


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
theorem _root_.solution (k : ℕ) (α mu : D.X) (y : (DegPre.BF D F).left) (J) :
    uVal D (FractionRing R) k α (cP D _ mu) (bc D F) y J = uVal D F k α (cP D _ mu) (𝟙 _) y J := by
  rw [uVal, uVal, bc_prB, Category.id_comp, Category.id_comp, comp_cP, comp_cP, comp_cP]
end GlobalTheory.FamBaseChange
