-- Prove2me | solution 1 for GlobalTheory.expandsAt_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:27.317303+00:00
-- url     : https://prove2.me/submissions/b0142ea1-2db3-4304-899c-54eb27a70dce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Theorems.Thm_GlobalTheory_gs_of_eq_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_expandsAt_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_expandsAt_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ₁ σ₂ σ : H0 U.LG.L k)
    (f₁ f₂ f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ j, σ.f j = σ₁.f j - σ₂.f j) →
    (∀ α j, (f α).f j = (f₁ α).f j - (f₂ α).f j) → U.ExpandsAt e k σ₁ f₁ → U.ExpandsAt e k σ₂ f₂ →
    U.ExpandsAt e k σ f := by
  intro R _ _ I D A G _ _ U e k σ₁ σ₂ σ f₁ f₂ f hσ hf h₁ h₂
  classical
  obtain ⟨S₁, H₁⟩ := ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U e k σ₁ f₁ h₁
  obtain ⟨S₂, H₂⟩ := ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U e k σ₂ f₂ h₂
  refine ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_of_val U e k σ f (S₁ ∪ S₂) ?_
  intro y J hJ
  obtain ⟨z1, e1⟩ := H₁ _ (𝟙 _) y J hJ
  obtain ⟨z2, e2⟩ := H₂ _ (𝟙 _) y J hJ
  simp only [Category.id_comp] at z1 z2 e1 e2
  have hs : ∀ α, sval (f α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J =
      sval (f₁ α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J - sval (f₂ α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J := by
    intro α
    first
      | exact gs_of_eq_sub _ _ _ (hf α _)
      | (unfold sval; exact gs_of_eq_sub _ _ _ (hf α _))
      | (simp only [sval]; exact gs_of_eq_sub _ _ _ (hf α _))
  refine ⟨fun α hα => ?_, fun jL hjL => ?_⟩
  · rw [hs α, z1 α (fun h => hα (Finset.mem_union_left _ h)),
      z2 α (fun h => hα (Finset.mem_union_right _ h)), sub_zero]
  · have hsv : ReciprocityTheory.ChartRestriction.G.DVR.sv U k σ (ReciprocityTheory.ChartRestriction.G.DVR.fGl I G e) y jL =
        ReciprocityTheory.ChartRestriction.G.DVR.sv U k σ₁ (ReciprocityTheory.ChartRestriction.G.DVR.fGl I G e) y jL -
          ReciprocityTheory.ChartRestriction.G.DVR.sv U k σ₂ (ReciprocityTheory.ChartRestriction.G.DVR.fGl I G e) y jL := by
      unfold ReciprocityTheory.ChartRestriction.G.DVR.sv
      exact gs_of_eq_sub _ _ _ (hσ _)
    have s1 := Finset.sum_subset (Finset.subset_union_left (s₂ := S₂))
      (fun α (_ : α ∈ S₁ ∪ S₂) (hα : α ∉ S₁) => show
        sval (f₁ α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J * (val (ReciprocityTheory.ChartRestriction.G.DVR.tG U e α) (𝟙 _) y J).val = 0 by
          rw [z1 α hα, zero_mul])
    have s2 := Finset.sum_subset (Finset.subset_union_right (s₁ := S₁))
      (fun α (_ : α ∈ S₁ ∪ S₂) (hα : α ∉ S₂) => show
        sval (f₂ α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J * (val (ReciprocityTheory.ChartRestriction.G.DVR.tG U e α) (𝟙 _) y J).val = 0 by
          rw [z2 α hα, zero_mul])
    rw [hsv, mul_sub, e1 jL hjL, e2 jL hjL, s1, s2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [hs α, sub_mul]
end GlobalTheory
