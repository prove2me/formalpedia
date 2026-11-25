-- Prove2me | solution 1 for GlobalTheory.KeyVia.Via.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:06.310843+00:00
-- url     : https://prove2.me/submissions/94ab879f-ec0f-42ba-98da-13336ed4f238

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open GlobalTheory GlobalTheory.KeyVia
variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}
namespace GlobalTheory.KeyVia
namespace Via
theorem _root_.solution (hL : L.IsLB) {w : LB.Iso L' (L.pull φ)} {l : ℕ} {a' b' : ∀ i, Γ(Y, L'.U i)}
    {a : ∀ j, Γ(X, L.U j)} (ha : Via w l a' a) (hb : Via w l b' a) : a' = b' := by
  funext i
  refine fn_ext fun y hy => ?_
  obtain ⟨j, hj⟩ := exists_chart (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)) y
  have h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) := inf_le_left.trans (chart_le j)
  have e := (ha j i h).symm.trans (hb j i h)
  have hu : IsUnit ((show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l) :=
    (Units.isUnit (w.s (j, i))).pow l
  have e' := hu.mul_left_cancel e
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ (L.pull φ).U j ⊓ L'.U i := ⟨hj, hy⟩
  exact (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e').trans
    (gs_res (𝟙 Y) y inf_le_right hm _))
end Via
end GlobalTheory.KeyVia
