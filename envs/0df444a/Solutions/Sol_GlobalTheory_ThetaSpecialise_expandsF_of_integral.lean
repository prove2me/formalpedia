-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.expandsF_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:00.254616+00:00
-- url     : https://prove2.me/submissions/4b44cba3-ac2c-4a11-8429-7c1b5064d627

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Theorems.Thm_GlobalTheory_ThetaSpecialise_gs_pullOver
import Theorems.Thm_GlobalTheory_FieldBaseChange_isoRelM_iff
import Theorems.Thm_GlobalTheory_FieldBaseChange_secLin_iff_val
import Theorems.Thm_GlobalTheory_FieldBaseChange_sval_pullOver
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution {k : ℕ}
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}
    {u : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))}
    (hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ A.A.left) (z : Z) (j : U.LG.L.ι) (i : A.L.ι),
      (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) (f z) ∈ U.LG.L.U j → f z ∈ A.L.U i →
      gw u f z j i = isoVal w (f ≫ U.gen.inv.left) z j i)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : ∀ α y J, Good D.toPre.P.L y J →
      sval (s.s α) (𝟙 _) y J = sval (f α) (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y J)
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) t σ) :
    U.ExpandsF F k w t s := by
  have h₂ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)
  have n₃ : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  have h₃ : ((𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
      𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [Category.id_comp, Category.id_comp, h₂, Category.assoc, n₃, Category.comp_id]
  have h₄ : (𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) := by
    rw [← h₃]; simp only [Category.assoc]
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  refine ⟨extendSec U F k (genericSec U k σ), (isoRelM_iff w _ k _ h₂ _ (Category.id_comp _) _ _).2
    fun y i₂ i₁ a₂ a₁ => ?_, 1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE,
    (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  · have b₂ := (congrArg (fun q : _ ⟶ G.left => q y ∈ U.LG.L.U i₂) h₄).mpr a₂
    have b₁ := (congrArg (fun q : _ ⟶ A.A.left => q y ∈ A.L.U i₁) h₂).mpr a₁
    have e := ht _ (𝟙 _ ≫ (U.genF F).left) y (fun _ => i₂) (fun _ => i₁) (fun _ => b₂) (fun _ => b₁)
    rw [Fin.prod_univ_one, hu _ ((𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) y i₂ i₁ b₂ b₁, h₃, h₄] at e
    refine Eq.trans ?_ e
    rw [Category.id_comp (𝟙 _)]
    exact (gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k σ) (𝟙 _) y (fun _ => i₂)
      (fun _ => a₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition
        (fun _ => (Category.comp_id _).symm) σ _ y (fun _ => i₂) (fun _ => a₂))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact hs α y J hJ
end GlobalTheory.ThetaSpecialise
