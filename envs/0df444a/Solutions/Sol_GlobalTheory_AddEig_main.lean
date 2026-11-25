-- Prove2me | solution 1 for GlobalTheory.AddEig.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:51:16.118232+00:00
-- url     : https://prove2.me/submissions/4cfe4221-3ee7-4a0d-a7ff-ceddd3461963

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSumTmulLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionTensorEigenDiagonalThetaOrderTwo
import Theorems.Thm_GlobalTheory_AddEig_kappa_translate
import Theorems.Thm_GlobalTheory_AddEig_tensor_eq_smul
import Theorems.Thm_GlobalTheory_ThetaLin_lift_translT
import Theorems.Thm_GlobalTheory_ThetaLin_sval_of_isTwistPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
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
open GlobalTheory GlobalTheory.AddEig
namespace GlobalTheory.AddEig
theorem _root_.solution : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' u u' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → ∀ θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p), θ.pt ^ 2 = 1 → (∀ i, IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t i).sec (u i).sec ∧ IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t' i).sec (u' i).sec) → ∃ r : F, ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  intro hG S P F _ p th n t t' u u' ⟨κ, hκ, hA⟩ θ hθ hact
  have := P.isAb.comm
  obtain ⟨r, hr⟩ := kappa_translate hG P p κ hκ θ.pt hθ θ.φ θ.isGen
  refine ⟨r, ?_⟩
  have pt : ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u' i).sec (lift ρ y).left z J =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) *
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t' i).sec (lift ρ y).left z J := by
    intro T ρ x y z J hJ
    have hd : (ρ ≫ θ.pt) * (ρ ≫ θ.pt) = 1 := by
      rw [← MonObj.comp_mul, ← pow_two, hθ, MonObj.comp_one]
    have a₁ := hA T ρ x y z J hJ
    have a₂ := hA T ρ ((ρ ≫ θ.pt) * x) ((ρ ≫ θ.pt) * y) z J hJ
    rw [_root_.mul_mul_mul_comm (ρ ≫ θ.pt), hd, _root_.one_mul, _root_.mul_inv, _root_.mul_mul_mul_comm (ρ ≫ θ.pt),
      mul_inv_cancel, _root_.one_mul] at a₂
    have b := hr T ρ x y z J hJ
    have act : ∀ (v w : EA P p 2) (x : T ⟶ P.A), IsActOf P.A P.L ((2 : ℕ) : ℤ) θ v.sec w.sec →
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) w.sec (lift ρ x).left z J =
        (val (L := P.L) (K := Fin 2) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![2, -2])
          θ.φ (lift ρ x).left z J).val *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := fun v w x h => by
      refine (ThetaLin.sval_of_isTwistPull P.A h (lift ρ x).left z hJ).trans ?_
      rw [← Over.comp_left, ThetaLin.lift_translT]
    rw [a₁, ← _root_.mul_assoc, ← b, Units.val_mul, _root_.mul_assoc, ← a₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act _ _ x (hact i).1, act _ _ y (hact i).2, Units.val_mul]
    exact _root_.mul_mul_mul_comm _ _ _ _
  have : IsProper (fst (Over.mk p) P.A).left := by
    have := P.isAb.proper
    show IsProper (pullback.fst _ _)
    infer_instance
  refine tensor_eq_smul P.isLB (fst (Over.mk p) P.A).left (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left)
    (ε := fun _ => ((2 : ℕ) : ℤ)) u u' t t' r fun Z r₁ r₂ h z J hJ => ?_
  let T : Over S := Over.mk (r₁ ≫ (Over.mk p ⊗ P.A).hom)
  let R₁ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₁ rfl
  let R₂ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₂ (by
    show r₂ ≫ (Over.mk p ⊗ P.A).hom = r₁ ≫ (Over.mk p ⊗ P.A).hom
    rw [← Over.w (fst (Over.mk p) P.A), ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ p) h.symm)
  have hR : R₂ ≫ fst _ _ = R₁ ≫ fst _ _ := Over.OverMorphism.ext h.symm
  have q := pt T (R₁ ≫ fst _ _) (R₁ ≫ snd _ _) (R₂ ≫ snd _ _) z J hJ
  rw [lift_comp_fst_snd, show lift (R₁ ≫ fst _ _) (R₂ ≫ snd _ _) = R₂ by rw [← hR, lift_comp_fst_snd]] at q
  exact q
end GlobalTheory.AddEig
