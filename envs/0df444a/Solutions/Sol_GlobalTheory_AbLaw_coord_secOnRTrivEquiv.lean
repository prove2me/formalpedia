-- Prove2me | solution 1 for GlobalTheory.AbLaw.coord_secOnRTrivEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:26:45.63014+00:00
-- url     : https://prove2.me/submissions/4ab54df9-1040-4a03-85c4-a0187996ff3f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
namespace GlobalTheory.AbLaw
theorem _root_.solution (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] {V : X.Opens}
    (hV : V = ⊤) (r : R) (i : (Inh.trivLB X).ι) :
    SecOnR.coord (secOnRTrivEquiv f hV r) i = cst f _ r := by
  refine (SecOnR.coord_base_smul r _ i).trans ?_
  have e := SecOn.coord_chart_symm (Inh.trivLB_isLB X) PUnit.unit i (le_top : V ≤ ⊤) 1
  have e₂ : rs X (inf_le_left : V ⊓ ⊤ ≤ V) 1 *
      rs X (le_inf le_top le_top : V ⊓ ⊤ ≤ ⊤ ⊓ ⊤) 1 = 1 := by
    rw [map_one, map_one, _root_.one_mul]
  exact (congrArg (cst f _ r * ·) (e.trans e₂)).trans (_root_.mul_one _)
end GlobalTheory.AbLaw
