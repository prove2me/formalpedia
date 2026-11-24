-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.triv_pull_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:02.623294+00:00
-- url     : https://prove2.me/submissions/a348dc93-4e62-4118-9969-0fb0cc3bed48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {X Y Z Z' T : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.AbLaw.CubeGen
theorem _root_.solution (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) :
    Triv ((LB.LinComb L φ ε).pull r) ↔ TrivAt L φ ε r := by
  have mem : ∀ (J : PUnit → K → L.ι) (z : Z), z ∈ ((LB.LinComb L φ ε).pull r).U J ↔
      z ∈ LB.wchart L (fun k => r ≫ φ k) (J PUnit.unit) := fun J z =>
    mem_pull.trans ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k,
      fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k⟩
  have g : ∀ (J J' : PUnit → K → L.ι) (z : Z), z ∈ ((LB.LinComb L φ ε).pull r).U J →
      z ∈ ((LB.LinComb L φ ε).pull r).U J' →
      gm (𝟙 Z) z (((LB.LinComb L φ ε).pull r).U J ⊓ ((LB.LinComb L φ ε).pull r).U J')
        (((LB.LinComb L φ ε).pull r).g J J') =
      gm (𝟙 Z) z (LB.wchart L (fun k => r ≫ φ k) (J PUnit.unit) ⊓ LB.wchart L (fun k => r ≫ φ k) (J' PUnit.unit))
        ((LB.LinComb L (fun k => r ≫ φ k) ε).g (J PUnit.unit) (J' PUnit.unit)) := fun J J' z h h' => by
    refine (gm_pull_g (LB.LinComb L φ ε) r (𝟙 Z) z J J' h h').trans ?_
    refine (gm_linComb L φ ε (𝟙 Z ≫ r) z _ _ (mem_pull.1 h) (mem_pull.1 h')).trans ?_
    refine Eq.trans ?_ (gm_linComb L (fun k => r ≫ φ k) ε (𝟙 Z) z _ _ ((mem J z).1 h) ((mem J' z).1 h')).symm
    simp only [Category.assoc]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨⟨fun j => res (fun z hz => (mem (fun _ => j) z).2 hz) (t.s fun _ => j)⟩,
      fun j j' => unit_ext fun z hz => ?_⟩
    have hm : (𝟙 Z : Z ⟶ Z) z ∈ ((LB.LinComb L φ ε).pull r).U (fun _ => j) ⊓
      ((LB.LinComb L φ ε).pull r).U (fun _ => j') := ⟨(mem _ z).2 hz.1, (mem _ z).2 hz.2⟩
    have e := congrArg (gm (𝟙 Z) z _) (ht (fun _ => j) (fun _ => j'))
    have e' := (gm_res _ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (g _ _ z hm.1 hm.2) (gm_res _ z _ hm _))))
    exact ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.1 _)).trans (e'.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.2 _)))).symm)
  · rintro ⟨t, ht⟩
    refine ⟨⟨fun J => res (fun z hz => (mem J z).1 hz) (t.s (J PUnit.unit))⟩,
      fun J J' => unit_ext fun z hz => ?_⟩
    have hm : (𝟙 Z : Z ⟶ Z) z ∈ LB.wchart L (fun k => r ≫ φ k) (J PUnit.unit) ⊓
      LB.wchart L (fun k => r ≫ φ k) (J' PUnit.unit) := ⟨(mem _ z).1 hz.1, (mem _ z).1 hz.2⟩
    have e := congrArg (gm (𝟙 Z) z _) (ht (J PUnit.unit) (J' PUnit.unit))
    have e' := (gm_res _ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (g _ _ z hz.1 hz.2).symm (gm_res _ z _ hm _))))
    exact ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.1 _)).trans (e'.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.2 _)))).symm)
end GlobalTheory.AbLaw.CubeGen
