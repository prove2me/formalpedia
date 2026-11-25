-- Prove2me | solution 1 for GlobalTheory.SimilUnit.IsVal.exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:02.209314+00:00
-- url     : https://prove2.me/submissions/18ac024f-9712-40be-82d9-d2ddb853dc36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNormalisingUnitSimilitudeOrigin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
open GlobalTheory GlobalTheory.SimilUnit
variable {X Y Y' : Scheme.{0}} (L : LB X)
variable {L} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
  {v v' : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ}
namespace GlobalTheory.SimilUnit
namespace IsVal
theorem _root_.solution (hL : L.IsLB) (a : IsVal L F v)
    (h1 : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = 1) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ y J, Good L y J → (v y J).val = gs (𝟙 Y) y ⊤ u.val := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨t', -, hv'⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => ((hF U h).trans (h1 U h)).trans (Fintype.prod_empty _).symm) t ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t'.s PEmpty.elim), fun y J hJ => ?_⟩
  rw [← hv y J hJ, ← hv' _ _ y J hJ, val_of t' _ y J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res _ y le trivial _)).symm.trans (gs_unit _ y ⊤ trivial _).symm
end IsVal
end GlobalTheory.SimilUnit
