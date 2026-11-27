-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.pullG_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:38.526107+00:00
-- url     : https://prove2.me/submissions/508b437d-3c14-4af3-ba26-be76096d15a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


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
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU.RelModel
theorem _root_.solution (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ)
    (σ : U.SecGT T k) {t t'} (h : U.PullG F φ k σ t) (h' : U.PullG F φ k σ t') (j) : t.f j = t'.f j := by
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ))
    A.isLB (fun z JA hA => ?_) j
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  let y : (TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left := (snd (TFK (R := R) F) A.A ≫ U.gen.inv).left
  have w : ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ T.hom = (y ≫ pullback.fst G.hom (jK R)) ≫ G.hom := by
    have a : y ≫ pullback.snd G.hom (jK R) = (TFK (R := R) F ⊗ A.A).hom := Over.w (snd (TFK (R := R) F) A.A ≫ U.gen.inv)
    have b : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (TFK (R := R) F ⊗ A.A).hom := Over.w (fst (TFK (R := R) F) A.A)
    have c : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    rw [Category.assoc y, pullback.condition, ← Category.assoc y, a, ← b, Category.assoc, Category.assoc]
    exact congrArg _ c
  let rG : (TFK (R := R) F ⊗ A.A).left ⟶ (T ⊗ G).left := pullback.lift _ _ w
  have e1 : 𝟙 _ ≫ (snd (TFK (R := R) F) A.A).left = y ≫ U.gen.hom.left := by
    rw [Category.id_comp, ← Over.comp_left, Category.assoc, U.gen.inv_hom_id, Category.comp_id]
  have e2 : rG ≫ (snd T G).left = y ≫ pullback.fst G.hom (jK R) := pullback.lift_snd _ _ _
  have e3 : rG ≫ (fst T G).left = 𝟙 _ ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left :=
    (pullback.lift_fst _ _ _).trans (Category.id_comp _).symm
  have := (h _ _ y rG e1 e2 e3 z JA JG hA hG).trans (h' _ _ y rG e1 e2 e3 z JA JG hA hG).symm
  exact ((Units.isUnit _).pow k).mul_left_cancel this
end GlobalTheory.UU.RelModel
