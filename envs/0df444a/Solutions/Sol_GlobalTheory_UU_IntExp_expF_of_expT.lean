-- Prove2me | solution 1 for GlobalTheory.UU.IntExp.expF_of_expT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:43.792803+00:00
-- url     : https://prove2.me/submissions/b581b1f0-f79d-4acc-a235-d7319f25490f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFOfExpT
import Theorems.Thm_GlobalTheory_UU_IntExp_sval_comp
import Theorems.Thm_GlobalTheory_UU_IntExp_gs_scal_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.IntExp
namespace GlobalTheory.UU.IntExp
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (t) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f → U.PullG F (toUnit _) k σ t → PullB D F (toUnit _) k f s → U.ExpF F k t s := by
  intro R _ _ I D A G _ _ U F _ _ k σ f t s hE hG hB
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE, ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    rw [Fin.sum_univ_one]
    refine (hG Z rA y rG h₁ h₂ ?_ z JA JG hJA hJG).trans ?_
    · have e₁ : (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left = (snd (𝟙_ _) G).left ≫ G.hom := by
        have a := Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        have b := Over.w (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        exact ((Category.comp_id _).symm.trans a).trans b.symm
      have e₂ : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R := by
        have a := Over.w (toUnit (TF (R := R) F))
        exact (Category.comp_id _).symm.trans a
      have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
        (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
      have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
      calc rG ≫ (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left
          = (rG ≫ (snd (𝟙_ _) G).left) ≫ G.hom := by rw [e₁]; exact (Category.assoc _ _ _).symm
        _ = y ≫ pullback.fst G.hom (jK R) ≫ G.hom := by rw [h₂]; exact Category.assoc _ _ _
        _ = y ≫ (U.gen.hom.left ≫ A.A.hom) ≫ jK R := by rw [e₄]; exact congrArg (y ≫ ·) pullback.condition
        _ = (rA ≫ (snd (TFK (R := R) F) A.A).left) ≫ A.A.hom ≫ jK R := by rw [h₁]; simp only [Category.assoc]
        _ = rA ≫ ((fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F) ≫ jK R := by rw [e₃]; simp only [Category.assoc]
        _ = _ := by rw [e₂]; exact congrArg (rA ≫ ·) (Category.assoc _ _ _)
    · exact ((congrArg (· * _) (gs_scal_one rA z _)).trans (one_mul _)).symm
  · intro α Z rF rB h z J hJ
    rw [Fin.sum_univ_one]
    refine Eq.trans ?_ ((congrArg (· * _) (gs_scal_one rF z _)).trans (one_mul _)).symm
    have e : rB = rF ≫ (toUnit (TF (R := R) F) ▷ D.P.A).left := by
      have w : (toUnit (TF (R := R) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
        congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := R) F)) D.P.A)
      have i : IsIso (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left := by
        rw [← leftUnitor_hom]; exact inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
      rw [← cancel_mono (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left, Category.assoc, w, h]
    rw [e, sval_comp (f α) _ rF z J hJ, ← hB α (rF z) _ (fun ψ => hJ (rF ≫ ψ)), ← sval_comp (s α) _ rF z J hJ,
      Category.comp_id]
end GlobalTheory.UU.IntExp
