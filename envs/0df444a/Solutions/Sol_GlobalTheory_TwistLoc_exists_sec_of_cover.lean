-- Prove2me | solution 1 for GlobalTheory.TwistLoc.exists_sec_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:26:10.101487+00:00
-- url     : https://prove2.me/submissions/eb722ae9-ae1a-4c41-b13b-00e97df9dc03

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.TwistLoc
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) {I : Type} (V : I → Y.Opens)
    (hV : ∀ y, ∃ i, y ∈ V i) (p : I → K → L.ι) (hp : ∀ i, V i ≤ LB.wchart L φ (p i)) (a : ∀ i, Γ(Y, V i))
    (ha : ∀ i i' y, y ∈ V i → y ∈ V i' →
      gs (𝟙 Y) y _ (a i) = (trF φ ε (𝟙 Y) y (p i) (p i')).val * gs (𝟙 Y) y _ (a i')) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : I) (j : K → L.ι),
      r z ∈ V i → r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j) (s.f j) = (trF φ ε r z j (p i)).val * gs r z _ (a i) := by
  have glue : ∀ j : K → L.ι, ∃ s : Γ(Y, LB.wchart L φ j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : I),
      r z ∈ V i → r z ∈ LB.wchart L φ j → gs r z _ s = (trF φ ε r z j (p i)).val * gs r z _ (a i) := by
    intro j
    let W : I → Y.Opens := fun i => LB.wchart L φ j ⊓ V i
    have le : ∀ i, W i ≤ LB.wchart L φ j ⊓ LB.wchart L φ (p i) := fun i => inf_le_inf_left _ (hp i)
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y, W i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ W i →
        gs r z (W i) (u i) = (trF φ ε r z j (p i)).val * gs r z _ (a i) :=
      ⟨fun i => (Y.presheaf.map (homOfLE (le i)).op).hom ((LB.LinComb L φ ε).g j (p i)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W i ≤ V i)).op).hom (a i), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans ((gs_unit r z _ (le i hz) _).trans
          (congrArg Units.val (gm_linComb L φ ε r z _ _ hz.1 (hp i hz.2))))) (gs_res r z _ hz _))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L φ j)
      (fun i => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := hV y
        exact Opens.mem_iSup.2 ⟨i, hy, hi⟩) u
      (fun i i' => fn_ext (V := W i ⊓ W i') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y i hy.1, hu _ _ y i' hy.2, ha i i' y hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          trF_trans hL φ ε (𝟙 Y) y hy.1.1 (hp i hy.1.2) (hp i' hy.2.2)])
    refine ⟨s, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ W i := ⟨h₂, h₁⟩
    exact (gs_res r z inf_le_left hz s).symm.trans ((congrArg (gs r z (W i)) (hs i)).trans (hu Z r z i hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z i j => hs j Z r z i⟩
  obtain ⟨i, hi⟩ := hV y
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hs j _ (𝟙 Y) y i hi hy.1).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y i hi hy.2)).symm)
  rw [← trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hp i hi), Units.val_mul, _root_.mul_assoc]; rfl
end GlobalTheory.TwistLoc
