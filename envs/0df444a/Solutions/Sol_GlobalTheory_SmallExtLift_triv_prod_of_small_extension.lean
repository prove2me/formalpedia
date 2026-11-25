-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.triv_prod_of_small_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:56.916257+00:00
-- url     : https://prove2.me/submissions/cc5f0cf9-4156-412e-9772-fe93414e3711

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TrivProdOfSmallExtension
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_kuenneth_injective
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_cocycle_fibre
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_gen
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_gen_fibre
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_slice
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_slice_fibre
import Theorems.Thm_GlobalTheory_SmallExtLift_exists_lift
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_appLE
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.SmallExtLift
namespace GlobalTheory.SmallExtLift
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → Triv (M.pull π) → Triv M := by
  intro R _ _ ε hm A B x₀ y₀ fA fB pA pB hA hB M hM ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ X' π f' P hε ⟨t, ht⟩
  have hεε : ε * ε = 0 := hm ε hε
  have sep : IsSeparated (A ⊗ B).hom := by
    change IsSeparated (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  have fl : Flat (A ⊗ B).hom := by
    change Flat (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  have : (A ⊗ B).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (A ⊗ B).hom]; infer_instance⟩
  obtain ⟨I, V, j, hj, u, α, hV, haff, hu, H⟩ := exists_lift hεε P hM t ht
  by_cases h0 : ε = 0
  · exact H.gen hεε hM hV hu (fun _ => 0) fun a b x ha hb => by rw [h0, map_zero, zero_mul]
  let φ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))
  let F := Over.pullback φ
  have kA : IsProper (F.obj A).hom := by
    change IsProper (pullback.snd A.hom φ); infer_instance
  have kB : IsProper (F.obj B).hom := by
    change IsProper (pullback.snd B.hom φ); infer_instance
  let i : (F.obj A ⊗ F.obj B).left ⟶ (A ⊗ B).left :=
    (Functor.Monoidal.μIso F A B).hom.left ≫ pullback.fst (A ⊗ B).hom φ
  have Pk : IsPullback i (F.obj A ⊗ F.obj B).hom (A ⊗ B).hom φ := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback (A ⊗ B).hom φ)
      ((Over.forget _).mapIso (Functor.Monoidal.μIso F A B).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · change _ ≫ 𝟙 _ = (Functor.Monoidal.μIso F A B).inv.left ≫ i
      rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id]
      simp
    · exact (Category.comp_id _).trans (Over.w (Functor.Monoidal.μIso F A B).inv).symm
  have slice : ∀ (C : Over (Sp R)) [Flat C.hom], Function.Bijective
      (pullback.snd C.hom q).appTop.hom → ∀ (s : C ⟶ A ⊗ B) (r : A ⊗ B ⟶ C) [IsSeparated r.left],
      s ≫ r = 𝟙 C →
      ∀ (t : LB.Gen (M.pull s.left)), t.IsGen → ∀ sk : F.obj C ⟶ F.obj A ⊗ F.obj B,
      sk ≫ (Functor.Monoidal.μIso F A B).hom = F.map s → _ := fun C _ hC s r _ hs t ht sk e => by
    have h1 : s.left ≫ r.left = 𝟙 _ := congrArg (fun q => q.left) hs
    have : IsClosedImmersion (s.left ≫ r.left) := by rw [h1]; infer_instance
    have : IsClosedImmersion s.left := IsClosedImmersion.of_comp s.left r.left
    have : Flat (s.left ≫ (A ⊗ B).hom) := by rw [Over.w]; infer_instance
    exact H.slice_fibre (i := i) hεε h0 hV haff s.left (π := pullback.fst C.hom q)
      (f' := pullback.snd C.hom q) (by rw [Over.w]; exact IsPullback.of_hasPullback _ _)
      hC.2 hu t ht (iA := pullback.fst C.hom φ)
      (fk := pullback.snd C.hom φ) (by rw [Over.w]; exact pullback.condition) sk.left (by
        rw [← Category.assoc, ← Over.comp_left, e]
        exact pullback.lift_fst _ _ _)
  have one : ∀ (C D : Over (Sp R)) (z : 𝟙_ (Over (Sp R)) ⟶ D),
      toUnit (F.obj C) ≫ Functor.LaxMonoidal.ε F ≫ F.map z = F.map (toUnit C ≫ z) := fun C D z => by
    rw [F.map_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Functor.OplaxMonoidal.η F)]
    exact toUnit_unique _ _
  obtain ⟨ψ, hψ⟩ := GlobalTheory.KuennethOne.kuenneth_injective (IsLocalRing.ResidueField R) (F.obj A)
    (F.obj B) (Functor.LaxMonoidal.ε F ≫ F.map x₀) (Functor.LaxMonoidal.ε F ≫ F.map y₀)
    inferInstance inferInstance inferInstance inferInstance
    (hA _ _ _ _ _ (IsPullback.of_hasPullback A.hom φ))
    (hB _ _ _ _ _ (IsPullback.of_hasPullback B.hom φ)) I
    (fun a => i ⁻¹ᵁ V a) (by rw [← Scheme.Hom.preimage_iSup, hV]; rfl)
    (fun a b => (i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b))
    (fun a b d => gr_ext fun y hy => by
      rw [map_add, gr_res, gr_res, gr_res, gr_appLE, gr_appLE, gr_appLE]
      exact H.cocycle_fibre hεε h0 hM haff hu Pk.w a b d y hy.1.1 hy.1.2 hy.2)
    (@slice A _ (hA _ _ _ _ _ (IsPullback.of_hasPullback A.hom q)) _ (fst A B)
      (by change IsSeparated (pullback.fst A.hom B.hom); infer_instance)
      (by simp) t₁ ht₁ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
    (@slice B _ (hB _ _ _ _ _ (IsPullback.of_hasPullback B.hom q)) _ (snd A B)
      (by change IsSeparated (pullback.snd A.hom B.hom); infer_instance)
      (by simp) t₂ ht₂ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
  exact H.gen_fibre hεε hm hM hV haff hu Pk ψ hψ
end GlobalTheory.SmallExtLift
