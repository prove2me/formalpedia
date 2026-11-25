-- Prove2me | solution 1 for GlobalTheory.AddGeneric.addA_of_addG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:40.160599+00:00
-- url     : https://prove2.me/submissions/c4b132a6-9830-463b-951b-53c5476bf808

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsAdditionFactorGeneratorTransported
import Theorems.Thm_GlobalTheory_AddGeneric_exists_additionFactor_generator_transported
import Theorems.Thm_GlobalTheory_AddGeneric_cancel_alg
import Theorems.Thm_GlobalTheory_AddGeneric_isUnit_scal
import Theorems.Thm_GlobalTheory_ThetaBaseChange_exists_unpull
import Theorems.Thm_GlobalTheory_UU_IsWt_add
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_toBase_mul_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_left


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
open GlobalTheory GlobalTheory.AddGeneric
namespace GlobalTheory.AddGeneric
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (θ : U.SecGT (𝟙_ _) 1) (r : R) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := R) F))) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := R) F))), r ≠ 0 → U.AddG θ r σ σ' → U.PullG F (toUnit _) 1 θ th → (∀ i, U.PullG F (toUnit _) 2 (σ i) (t i) ∧ U.PullG F (toUnit _) 2 (σ' i) (t' i)) → AddA A (TFK (R := R) F) th t t' := by
  intro R _ _ D I A G _ _ U F _ _ θ r n σ σ' th t t' hr hadd hθ hσ
  have := U.gen_hom
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  obtain ⟨u, hu, huv⟩ := ThetaBaseChange.exists_unpull U.wA_gen U.gen.inv.left hi rfl
  have hw : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ G.hom = A.A.hom ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ jK R) (Over.w U.gen.inv)
  have tb : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), toBase hw x =
      toBase (A := G) (A' := (Over.pullback (jK R)).obj G) (g := pullback.fst G.hom (jK R)) pullback.condition
        (x ≫ U.gen.inv) := fun T x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
  have mul : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x y : T ⟶ A.A),
      toBase hw (x * y) = toBase hw x * toBase hw y := fun T x y => by
    rw [tb, tb, tb, MonObj.mul_comp, toBase_mul_pullback]
  obtain ⟨a, ha, hv⟩ := exists_additionFactor_generator_transported U.P hw mul A.isLB u hu (Y := TFK (R := R) F ⊗ (A.A ⊗ A.A))
    (snd _ _ ≫ fst A.A A.A) (snd _ _ ≫ snd A.A A.A) (snd _ _ ≫ (fst A.A A.A * snd A.A A.A))
    (snd _ _ ≫ (fst A.A A.A * (snd A.A A.A)⁻¹)) (MonObj.comp_mul _ _ _)
    ((MonObj.comp_mul _ _ _).trans (by rw [GrpObj.comp_inv]))
  have hun := isUnit_scal (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom hr
  refine ⟨scaleGen hun.unit a, scaleGen_isGen _ ha, fun T ρ x y z J hJ => ?_⟩
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let W : (T ⟶ A.A) → (T.left.presheaf.stalk z)ˣ := fun p =>
    gw u p.left z (JG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (J p.left)
  have k₀ := hv T (lift ρ (lift x y)) z JG J hJG hJ W (fun _ => rfl)
  have ex : lift ρ (lift x y) ≫ snd _ _ ≫ fst A.A A.A = x := by simp
  have ey : lift ρ (lift x y) ≫ snd _ _ ≫ snd A.A A.A = y := by simp
  rw [ex, ey] at k₀
  have pull : ∀ (k : ℕ) (s : U.SecGT (𝟙_ _) k) (s' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))),
      U.PullG F (toUnit _) k s s' → ∀ p : T ⟶ A.A,
      (W p).val ^ k * sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ))
        s' (lift ρ p).left z J =
      @id (T.left.presheaf.stalk z) (sval s (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left z JG) := by
    intro k s s' h p
    have e₁ : (p.left ≫ U.gen.inv.left) ≫ U.gen.hom.left = p.left := by rw [Category.assoc, hi, Category.comp_id]
    have e := h T.left (lift ρ p).left (p.left ≫ U.gen.inv.left)
      (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left
      ((congrArg (fun q => q.left) (lift_snd ρ p)).trans e₁.symm)
      ((congrArg (fun q => q.left) (lift_snd _ (toBase hw p))).trans (Category.assoc _ _ _).symm)
      (by
        rw [← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Rosenlicht.toUnit_left, Rosenlicht.toUnit_left]
        show T.hom ≫ jK R = ρ.left ≫ jFK (R := R) F ≫ jK R
        rw [← Category.assoc]
        exact congrArg (· ≫ jK R) (Over.w ρ).symm) z J JG hJ hJG
    rw [e₁, Category.assoc] at e
    refine Eq.trans (congrArg (fun q : (T.left.presheaf.stalk z)ˣ => q.val ^ k * _) ?_) e
    exact huv _ p.left z _ _ (hJG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (hJ p.left)
  have add := hadd (Over.mk (T.hom ≫ jK R)) (toBase hw x) (toBase hw y) z JG hJG
  have e : toBase hw (x * y⁻¹) = toBase hw x * (toBase hw y)⁻¹ :=
    (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul T) y))
  rw [← e, ← mul] at add
  have key := cancel_alg (W x) (W y) (W (x * y)) (W (x * y⁻¹)) _ _ _ _ _ _ _ k₀
    ((Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (pull 2 _ _ (hσ i).1 x) (pull 2 _ _ (hσ i).2 y)).trans
      (add.trans (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (pull 1 _ _ hθ _).symm (pull 1 _ _ hθ _).symm))))
  refine key.trans (congrArg (· * _) ?_)
  rw [val_scaleGen _ _ _ hJ, Units.val_mul]
  refine congrArg (· * _) (Eq.trans ?_ (gs_unit _ z ⊤ trivial _))
  refine Eq.trans ?_ ((gs_pull (𝟙 _) (lift ρ (lift x y)).left z ⊤ trivial _).trans (by rw [Category.id_comp]))
  refine congrArg (gs (𝟙 T.left) z ⊤) ?_
  show scal (T.hom ≫ jK R) r = scal ((lift ρ (lift x y)).left ≫ (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom ≫ jK R) r
  rw [← Category.assoc, Over.w]
end GlobalTheory.AddGeneric
