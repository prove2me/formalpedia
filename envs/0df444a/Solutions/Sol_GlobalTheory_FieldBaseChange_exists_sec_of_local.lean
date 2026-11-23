-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.exists_sec_of_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:09.916073+00:00
-- url     : https://prove2.me/submissions/fe15ced5-3a0f-40c6-8c56-40a834179ef1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_glue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {Y Y' X₁ X₂ Z₁ Z₂ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution {L : LB X₂} {g : Y' ⟶ X₂} {k : ℤ} {I : Type} (W : I → Y'.Opens)
    (hW : ∀ y, ∃ p, y ∈ W p)
    (u : ∀ (i : L.ι) (p : I), Γ(Y', LB.wchart L (fun _ : Fin 1 => g) (fun _ => i) ⊓ W p))
    (v : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y') (z : Z), L.ι → I → Z.presheaf.stalk z)
    (huv : ∀ Z r z i p, g (r z) ∈ L.U i → r z ∈ W p → gs r z _ (u i p) = v Z r z i p)
    (h₁ : ∀ y i p p', g y ∈ L.U i → y ∈ W p → y ∈ W p' → v _ (𝟙 Y') y i p = v _ (𝟙 Y') y i p')
    (h₂ : ∀ y i i' p, g y ∈ L.U i → g y ∈ L.U i' → y ∈ W p →
      v _ (𝟙 Y') y i p = (gm (𝟙 Y' ≫ g) y _ (L.g i i') ^ k).val * v _ (𝟙 Y') y i' p) :
    ∃ b : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k)),
      ∀ Z r z i p, g (r z) ∈ L.U i → r z ∈ W p → powVal b r z i = v Z r z i p := by
  have glue : ∀ i : L.ι, ∃ a : Γ(Y', LB.wchart L (fun _ : Fin 1 => g) (fun _ => i)),
      ∀ Z r z p, g (r z) ∈ L.U i → r z ∈ W p → gs r z _ a = v Z r z i p := fun i => by
    obtain ⟨a, ha, -⟩ := sec_glue (LB.wchart L (fun _ : Fin 1 => g) (fun _ => i))
      (fun p => LB.wchart L (fun _ : Fin 1 => g) (fun _ => i) ⊓ W p) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨p, hp⟩ := hW y
        exact Opens.mem_iSup.2 ⟨p, hy, hp⟩) (u i) (fun p p' => fn_ext fun y hy => by
        have hi := mem_wchart.1 hy.1.1 0
        exact ((gs_res (𝟙 Y') y inf_le_left hy _).trans (huv _ _ y i p hi hy.1.2)).trans
          ((h₁ y i p p' hi hy.1.2 hy.2.2).trans
            ((gs_res (𝟙 Y') y inf_le_right hy _).trans (huv _ _ y i p' hi hy.2.2)).symm))
    refine ⟨a, fun Z r z p hi hp => ?_⟩
    have hz : r z ∈ LB.wchart L (fun _ : Fin 1 => g) (fun _ => i) ⊓ W p := ⟨mem_wchart.2 fun _ => hi, hp⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha p)).trans (huv Z r z i p hi hp))
  have glue' : ∀ j : Fin 1 → L.ι, ∃ a : Γ(Y', LB.wchart L (fun _ : Fin 1 => g) j),
      ∀ Z r z p, g (r z) ∈ L.U (j 0) → r z ∈ W p → gs r z _ a = v Z r z (j 0) p := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun t => congrArg j (Subsingleton.elim _ _)⟩
    exact glue i
  choose a ha using glue'
  refine ⟨⟨a, fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => ?_⟩, fun Z r z i p hi hp => ha _ Z r z p hi hp⟩
  obtain ⟨p, hp⟩ := hW y
  have m := mem_wchart.1 hy.1 0
  have m' := mem_wchart.1 hy.2 0
  refine ((gs_res (𝟙 Y') y _ hy _).trans (ha j _ _ y p m hp)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans (congrArg Units.val
      ((gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2).trans (Fin.prod_univ_one _))))
      ((gs_res (𝟙 Y') y _ hy _).trans (ha j' _ _ y p m' hp)))).symm)
  exact h₂ y _ _ p m m' hp
end GlobalTheory.FieldBaseChange
