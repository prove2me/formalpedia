-- Prove2me | solution 1 for GlobalTheory.SS.FrobLB.gen_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:09.152872+00:00
-- url     : https://prove2.me/submissions/fdc40dcd-9c7b-4ba0-aa60-f0315c4384e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPowOfFix
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobLB
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
namespace GlobalTheory.SS.FrobLB
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {A : Type} (V : A → Y.Opens) (J : A → K → L.ι) (hc : ∀ y, ∃ a, y ∈ V a) (hV : ∀ a, V a ≤ LB.wchart L φ (J a))
    (h1 : ∀ a b y, y ∈ V a → y ∈ V b → trF φ ε (𝟙 Y) y (J a) (J b) = 1) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have glue : ∀ j : K → L.ι, ∃ s : Γ(Y, LB.wchart L φ j)ˣ, ∀ a y, y ∈ LB.wchart L φ j → y ∈ V a →
      gm (𝟙 Y) y _ s = trF φ ε (𝟙 Y) y j (J a) := by
    intro j
    have le : ∀ a, LB.wchart L φ j ⊓ V a ≤ LB.wchart L φ j ⊓ LB.wchart L φ (J a) :=
      fun a => inf_le_inf_left _ (hV a)
    have hu : ∀ a y, y ∈ LB.wchart L φ j ⊓ V a →
        gm (𝟙 Y) y _ (res (le a) ((LB.LinComb L φ ε).g j (J a))) = trF φ ε (𝟙 Y) y j (J a) := fun a y hy =>
      (gm_res (𝟙 Y) y (le a) hy _).trans (gm_linComb L φ ε (𝟙 Y) y j (J a) hy.1 (hV a hy.2))
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart L φ j) (fun a => LB.wchart L φ j ⊓ V a) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨a, ha⟩ := hc y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hy, ha⟩)
      (fun a => res (le a) ((LB.LinComb L φ ε).g j (J a))) (fun a b y hy => by
        refine (hu a y hy.1).trans (Eq.trans ?_ (hu b y hy.2).symm)
        rw [← trF_trans hL φ ε (𝟙 Y) y hy.1.1 (hV a hy.1.2) (hV b hy.2.2), h1 a b y hy.1.2 hy.2.2, _root_.mul_one])
    refine ⟨s, fun a y h₁ h₂ => ?_⟩
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j ⊓ V a := ⟨h₁, h₂⟩
    exact (gm_res (𝟙 Y) y inf_le_left hm s).symm.trans ((congrArg (gm (𝟙 Y) y _) (hs a)).trans (hu a y hm))
  choose s hs using glue
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  refine ((gm_res (𝟙 Y) y _ hy _).trans (hs j a y hy.1 ha)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (hs j' a y hy.2 ha))).trans ?_)
  exact trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hV a ha)
end GlobalTheory.SS.FrobLB
