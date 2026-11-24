-- Prove2me | solution 1 for GlobalTheory.BoxSpan.exists_sec_pw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:03:55.928172+00:00
-- url     : https://prove2.me/submissions/7ff2f76f-d35a-4fbd-94c3-28a9f16c6f13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxProductsBasisSpanPowObjSections
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.BoxSpan
variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
namespace GlobalTheory.BoxSpan
theorem _root_.solution (L : LB X) (t : ℤ) (a : LB.Sec (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => t))) :
    ∃ a' : LB.Sec (pw L t), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
      sval a r z J = gs r z (L.U (J r)) (a'.f (J r)) := by
  have hle : ∀ i, L.U i ≤ LB.wchart L (K := PUnit) (fun _ => 𝟙 X) (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  refine ⟨⟨fun i => rs X (hle i) (a.f fun _ => i), fun i j => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · have hy' : y ∈ L.U i ⊓ L.U j := hy
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (hle i) hy'.1 _)).trans
      ((sec_trans a (𝟙 X) y (hle i hy'.1) (hle j hy'.2)).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy _ _).symm))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (hle j) hy'.2 _)).symm
    refine Eq.trans ?_ (gs_unit (𝟙 X) y (L.U i ⊓ L.U j) hy' (L.g i j ^ t)).symm
    rw [map_zpow]
    exact congrArg Units.val (Fintype.prod_unique (fun _ : PUnit => gm (𝟙 X ≫ 𝟙 X) y (L.U i ⊓ L.U j) (L.g i j) ^ t))
  · rw [sval_of a r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact (gs_res r z (hle _) (hJ r) _).symm
end GlobalTheory.BoxSpan
