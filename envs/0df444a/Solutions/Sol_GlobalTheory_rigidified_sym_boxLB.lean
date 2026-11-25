-- Prove2me | solution 1 for GlobalTheory.rigidified_sym_boxLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:37.671749+00:00
-- url     : https://prove2.me/submissions/72229559-b459-4c90-a491-7b1d01f58180

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedSymBoxLB
import Theorems.Thm_GlobalTheory_BoxSymLoc_isGen_boxGen
import Theorems.Thm_GlobalTheory_BoxSymLoc_exists_restrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_isGen_pullAlong


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open BoxSymLoc ReciprocityTheory.ChartRestriction.G.Out.LBxP
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (_hL : L.IsLB) :
    (Rigidified G L → Rigidified G' (boxLB L p.pr)) ∧
      (Out.Sym G L → Out.Sym G' (boxLB L p.pr)) := by
  constructor
  · rintro ⟨t, ht⟩
    have he : ∀ i : Fin j, ∀ _k : PUnit, eSec G' ≫ (p.pr i).left = 𝟙 _ ≫ eSec G := by
      intro i _
      have := p.hom i
      rw [Category.id_comp, eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
    exact ⟨GeneratorPullback.boxGen L (fun i => (p.pr i).left) (fun _ => eSec G') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (p.pr i).left (𝟙 _) (fun _ => eSec G) _ _ (he i) t),
      isGen_boxGen L _ _ _ _ fun i => isGen_pullAlong L _ _ _ _ _ (he i) t ht⟩
  · intro h s
    obtain ⟨U, hs, t, ht⟩ := h s
    refine ⟨U, hs, ?_⟩
    choose ρ hρ using fun i => exists_restrict (p.pr i) U
    have he : ∀ i : Fin j, ∀ k : Fin 2,
        (![(G'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G' ⟶ G').left, (G'.hom ⁻¹ᵁ U).ι] :
          Fin 2 → ((G'.hom ⁻¹ᵁ U).toScheme ⟶ G'.left)) k ≫ (p.pr i).left =
        ρ i ≫ (![(G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ U).ι] :
          Fin 2 → ((G.hom ⁻¹ᵁ U).toScheme ⟶ G.left)) k := by
      intro i k
      have := p.hom i
      fin_cases k
      · have h0 : (GrpObj.inv : G' ⟶ G').left ≫ (p.pr i).left =
            (p.pr i).left ≫ (GrpObj.inv : G ⟶ G).left := inv_pr p i 0
        show ((G'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G' ⟶ G').left) ≫ (p.pr i).left =
          ρ i ≫ (G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left
        rw [Category.assoc, h0, ← Category.assoc, ← hρ i, Category.assoc]
      · exact (hρ i).symm
    exact ⟨GeneratorPullback.boxGen L (fun i => (p.pr i).left) _ _
      (fun i => GeneratorPullback.pullAlong L (p.pr i).left (ρ i) _ _ _ (he i) t),
      isGen_boxGen L _ _ _ _ fun i => isGen_pullAlong L _ _ _ _ _ (he i) t ht⟩
end GlobalTheory
