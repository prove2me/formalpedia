-- Prove2me | solution 1 for GlobalTheory.FamIntAt.exists_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:39.172155+00:00
-- url     : https://prove2.me/submissions/bfcb8c47-bccd-4015-bc6a-c4d26828a09a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
import Theorems.Thm_GlobalTheory_PsiInPull_gs_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FamIntAt
namespace GlobalTheory.FamIntAt
theorem _root_.solution {X Y Z : Scheme.{0}} [IsReduced Y] {L : LB X} (hL : L.IsLB) (ζ : Z ⟶ Y) (ξ : Z)
    (hξ : ∀ z : Z, z = ξ) (hd : ∀ U : Y.Opens, U ≠ ⊥ → ζ ξ ∈ U) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (t : LB.Sec (LB.LinComb L (fun k => ζ ≫ φ k) ε))
    (H : ∀ q : Y, ∃ (j : K → L.ι) (V : Y.Opens) (a : Γ(Y, V)), q ∈ V ∧ V ≤ LB.wchart L φ j ∧
      gs ζ ξ V a = gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j) (t.f j)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (T : Scheme.{0}) (r : T ⟶ Z) (z : T) (J), Good L z J →
      sval s (r ≫ ζ) z J = sval t r z J := by
  have inj : ∀ (V : Y.Opens) (a b : Γ(Y, V)), (ζ ξ ∈ V → gs ζ ξ V a = gs ζ ξ V b) → a = b := by
    intro V a b h
    by_cases hV : V = ⊥
    · exact fn_ext fun x hx => (hV.le hx : x ∈ (⊥ : Y.Opens)).elim
    · exact PsiInPull.gs_injective ζ ξ hd V (hd V hV) (h (hd V hV))
  have mem : ∀ {j : K → L.ι} {z : Z}, ζ z ∈ LB.wchart L φ j → (𝟙 Z : Z ⟶ Z) z ∈ LB.wchart L (fun k => ζ ≫ φ k) j :=
    fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k
  have tr : ∀ {j j' : K → L.ι}, ζ ξ ∈ LB.wchart L φ j → ζ ξ ∈ LB.wchart L φ j' →
      gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j) (t.f j) =
        gs ζ ξ (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val *
          gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j') (t.f j') := fun {j j'} h h' => by
    refine (sec_trans t (𝟙 Z) ξ (mem h) (mem h')).trans (congrArg₂ (· * ·) (Eq.symm ?_) rfl)
    refine (gs_unit ζ ξ _ (show ζ ξ ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' from ⟨h, h'⟩) _).trans
      (congrArg Units.val ((gm_linComb L φ ε ζ ξ j j' h h').trans ?_))
    simp only [trF, Category.id_comp]
  choose j₀ V a hq hV ha using H
  have glue : ∀ j : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ j), ζ ξ ∈ LB.wchart L φ j →
      gs ζ ξ _ b = gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j) (t.f j) := by
    intro j
    let W : Y → Y.Opens := fun q => LB.wchart L φ j ⊓ V q
    have l : ∀ q, W q ≤ LB.wchart L φ j ⊓ LB.wchart L φ (j₀ q) := fun q => inf_le_inf_left _ (hV q)
    obtain ⟨u, hu⟩ : ∃ u : ∀ q, Γ(Y, W q), ∀ q, ζ ξ ∈ W q →
        gs ζ ξ (W q) (u q) = gs (𝟙 Z) ξ (LB.wchart L (fun k => ζ ≫ φ k) j) (t.f j) :=
      ⟨fun q => (Y.presheaf.map (homOfLE (l q)).op).hom ((LB.LinComb L φ ε).g j (j₀ q)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W q ≤ V q)).op).hom (a q), fun q h =>
        (gs_mul ζ ξ _ h _ _).trans ((congrArg₂ (· * ·) (gs_res ζ ξ (l q) h _)
          ((gs_res ζ ξ inf_le_right h _).trans (ha q))).trans (tr h.1 (hV q h.2)).symm)⟩
    obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L φ j)
      (fun q => homOfLE inf_le_left) (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy, hq y⟩) u
      (fun q q' => inj (W q ⊓ W q') _ _ fun h =>
        (gs_res ζ ξ inf_le_left h _).trans ((hu q h.1).trans ((hu q' h.2).symm.trans
          (gs_res ζ ξ inf_le_right h _).symm)))
    refine ⟨b, fun h => ?_⟩
    have hz : ζ ξ ∈ W (ζ ξ) := ⟨h, hq _⟩
    exact (gs_res ζ ξ inf_le_left hz b).symm.trans ((congrArg (gs ζ ξ (W (ζ ξ))) (hb _)).trans (hu _ hz))
  choose b hb using glue
  refine ⟨⟨b, fun j j' => inj _ _ _ fun h => ?_⟩, fun T r z J hJ => ?_⟩
  · exact (gs_res ζ ξ _ h _).trans ((hb j h.1).trans ((tr h.1 h.2).trans (Eq.symm ((gs_mul ζ ξ _ h _ _).trans
      (congrArg₂ (· * ·) rfl ((gs_res ζ ξ _ h _).trans (hb j' h.2)))))))
  · rw [sval_of _ (r ≫ ζ) z J (fun k => J (r ≫ ζ ≫ φ k)) (fun k => by rw [Category.assoc])]
    have hm := hJ.mem (fun k => ζ ≫ φ k) r
    have le : LB.wchart L (fun k => ζ ≫ φ k) (fun k => J (r ≫ ζ ≫ φ k)) ≤
        ζ ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ ζ ≫ φ k)) :=
      fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    have e : (Z.presheaf.map (homOfLE le).op).hom ((ζ.app _).hom (b (fun k => J (r ≫ ζ ≫ φ k)))) =
        t.f (fun k => J (r ≫ ζ ≫ φ k)) := fn_ext fun y hy => by
      obtain rfl := hξ y
      refine (gs_res _ y le hy _).trans ((gs_pull _ ζ y _ (le hy) _).trans ?_)
      rw [Category.id_comp]
      exact hb _ (le hy)
    exact ((gs_res r z le hm _).trans (gs_pull r ζ z _ (le hm) _)).symm.trans (congrArg (gs r z _) e)
end GlobalTheory.FamIntAt
