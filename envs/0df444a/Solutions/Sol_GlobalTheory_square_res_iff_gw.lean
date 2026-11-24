-- Prove2me | solution 1 for GlobalTheory.square_res_iff_gw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:52.71961+00:00
-- url     : https://prove2.me/submissions/e8df0113-9644-417a-9bbc-56026e401c13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
import Theorems.Thm_GlobalTheory_gm_mul_eq_of_res_mul_eq
import Theorems.Thm_GlobalTheory_res_mul_eq_of_gm_mul_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution {X X' G G' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {L : LB G} {L' : LB G'}
    {F : X' ⟶ X} {B : G' ⟶ G} {p : Y ⟶ X} {p' : Y' ⟶ X'} {f : Y ⟶ G} {f' : Y' ⟶ G'} {h : Y' ⟶ Y}
    (hf : h ≫ f = f' ≫ B) (hp : p' ≫ F = h ≫ p)
    (wM : LB.Iso M' (M.pull F)) (wL : LB.Iso L' (L.pull B))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) :
    (∀ (jM : PUnit → M.ι) (jM' : M'.ι) (jL' : L'.ι) (jL : PUnit → L.ι),
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_left) :
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM') ⊓
            (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') ⊓
            h ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (jM, jL) ⊓
            f' ⁻¹ᵁ (LB.div (L.pull B) L').U (jL, jL') ≤
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM'))
        (pullU p' _ (wM.s (jM, jM'))) *
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (w'.s (fun _ => jM', fun _ => jL')) =
      res (X := Y') (inf_le_left.trans inf_le_right) (pullU h _ (w.s (jM, jL))) *
      res (X := Y') inf_le_right (pullU f' _ (wL.s (jL, jL')))) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      F (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → B (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL' := by
  have ef : ∀ y : Y', f (h y) = B (f' y) := fun y => congrArg (fun g => g y) hf
  have ep : ∀ y : Y', p (h y) = F (p' y) := fun y => congrArg (fun g => g y) hp.symm
  constructor
  · intro H Z r z jM jM' jL jL' h₁ h₂ h₃ h₄
    have m₁ : p' (r z) ∈ (LB.div (M.pull F) M').U (fun _ => jM, jM') := ⟨mem_pull.2 h₁, h₂⟩
    have m₂ : r z ∈ (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') :=
      ⟨mem_pull.2 h₂, mem_pull.2 h₄⟩
    have m₃ : h (r z) ∈ (LB.div (M.pull p) (L.pull f)).U (fun _ => jM, fun _ => jL) :=
      ⟨mem_pull.2 (by rw [ep]; exact h₁), mem_pull.2 (by rw [ef]; exact h₃)⟩
    have m₄ : f' (r z) ∈ (LB.div (L.pull B) L').U (fun _ => jL, jL') := ⟨mem_pull.2 h₃, h₄⟩
    have e := gm_mul_eq_of_res_mul_eq (H (fun _ => jM) jM' jL' (fun _ => jL)) r z ⟨⟨⟨m₁, m₂⟩, m₃⟩, m₄⟩
    rw [gm_pull r p' z _ m₁, gm_pull r h z _ m₃, gm_pull r f' z _ m₄] at e
    exact e
  · intro H jM jM' jL' jL
    refine res_mul_eq_of_gm_mul_eq fun y hy => ?_
    have e := H Y' (𝟙 Y') y (jM PUnit.unit) jM' (jL PUnit.unit) jL' (mem_pull.1 hy.1.1.1.1) hy.1.1.1.2
      (mem_pull.1 hy.2.1) hy.2.2
    rw [gm_pull (𝟙 Y') p' y _ hy.1.1.1, gm_pull (𝟙 Y') h y _ hy.1.2, gm_pull (𝟙 Y') f' y _ hy.2]
    exact e
end GlobalTheory
