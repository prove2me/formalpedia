-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2690668d-2313-588d-b3ae-a430c45bfc45

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace EF1nA4

p2m_open "Opposite CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory MonObj CategoryTheory.MonObj TensorProduct"

universe v₁ v₂ u₁ u₂

section alpha

variable {R : Type u} [CommRing R]

lemma comul_unop_def (A : (CommAlgCat.{u} R)ᵒᵖ) [MonObj A] :
    (Coalgebra.comul : A.unop →ₗ[R] A.unop ⊗[R] A.unop) = μ[A].unop.hom.toLinearMap := rfl

lemma counit_unop_def (A : (CommAlgCat.{u} R)ᵒᵖ) [MonObj A] :
    (Coalgebra.counit : A.unop →ₗ[R] R) = η[A].unop.hom.toLinearMap := rfl

lemma ofId_toLinearMap (B : Type u) [CommRing B] [Algebra R B] :
    (Algebra.ofId R B).toLinearMap = Algebra.linearMap R B :=
  LinearMap.ext fun _ => rfl

lemma lift_unop_hom_toLinearMap {X Y Z : (CommAlgCat.{u} R)ᵒᵖ} (f : Z ⟶ X) (g : Z ⟶ Y) :
    (CartesianMonoidalCategory.lift f g).unop.hom.toLinearMap =
      LinearMap.mul' R Z.unop ∘ₗ
        TensorProduct.map f.unop.hom.toLinearMap g.unop.hom.toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  simp [CommAlgCat.lift_unop_hom, Algebra.TensorProduct.lift_tmul]

noncomputable scoped instance hopfAlgebraUnop (A : (CommAlgCat.{u} R)ᵒᵖ) [GrpObj A] :
    HopfAlgebra R A.unop where
  antipode := ι[A].unop.hom.toLinearMap
  mul_antipode_rTensor_comul := by
    have h := congr(($(GrpObj.left_inv A)).unop.hom.toLinearMap)
    simp only [unop_comp, CommAlgCat.hom_comp, AlgHom.comp_toLinearMap,
      lift_unop_hom_toLinearMap, unop_id, CommAlgCat.hom_id, CommAlgCat.toUnit_unop_hom,
      AlgHom.toLinearMap_id, ofId_toLinearMap] at h
    rw [comul_unop_def, counit_unop_def, LinearMap.rTensor_def, ← LinearMap.comp_assoc]
    exact h
  mul_antipode_lTensor_comul := by
    have h := congr(($(GrpObj.right_inv A)).unop.hom.toLinearMap)
    simp only [unop_comp, CommAlgCat.hom_comp, AlgHom.comp_toLinearMap,
      lift_unop_hom_toLinearMap, unop_id, CommAlgCat.hom_id, CommAlgCat.toUnit_unop_hom,
      AlgHom.toLinearMap_id, ofId_toLinearMap] at h
    rw [comul_unop_def, counit_unop_def, LinearMap.lTensor_def, ← LinearMap.comp_assoc]
    exact h

lemma antipode_unop_def (A : (CommAlgCat.{u} R)ᵒᵖ) [GrpObj A] :
    HopfAlgebra.antipode R (A := A.unop) = ι[A].unop.hom.toLinearMap := rfl

scoped instance isCocommUnop (A : (CommAlgCat.{u} R)ᵒᵖ) [MonObj A] [IsCommMonObj A] :
    Coalgebra.IsCocomm R A.unop where
  comm_comp_comul := by
    have h := congr(($(IsCommMonObj.mul_comm A)).unop.hom.toLinearMap)
    simp only [unop_comp, CommAlgCat.hom_comp, AlgHom.comp_toLinearMap, unop_hom_braiding,
      CommAlgCat.braiding_hom_hom] at h
    rw [comul_unop_def]
    convert h using 2 <;> rfl

end alpha

section epsilon
p2m_open "Functor CategoryTheory.Functor CategoryTheory.MonoidalCategory.Functor CategoryTheory.Functor.OplaxMonoidal"

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.OplaxMonoidal]

lemma map_hom_mul {X : C} [MonObj X] [MonObj (F.obj X)]
    (hμ : F.map μ[X] = δ F X X ≫ μ[F.obj X]) {Y : C} (f g : Y ⟶ X) :
    F.map (f * g) = F.map f * F.map g := by
  simp only [Hom.mul_def, Functor.map_comp, hμ, lift_δ_assoc]

lemma map_hom_one {X : C} [MonObj X] [MonObj (F.obj X)]
    (hη : F.map η[X] = OplaxMonoidal.η F ≫ η[F.obj X]) (Y : C) :
    F.map (1 : Y ⟶ X) = 1 := by
  simp only [Hom.one_def, Functor.map_comp, hη, η_of_cartesianMonoidalCategory,
    CartesianMonoidalCategory.terminalComparison, comp_toUnit_assoc]

variable (hF : F.FullyFaithful) (X : C)

lemma map_mul_monObj [MonObj (F.obj X)] :
    letI := hF.monObj X; F.map μ[X] = δ F X X ≫ μ[F.obj X] := by
  simp

lemma map_one_monObj [MonObj (F.obj X)] :
    letI := hF.monObj X; F.map η[X] = OplaxMonoidal.η F ≫ η[F.obj X] := by
  simp

abbrev grpObjOfFullyFaithful [GrpObj (F.obj X)] : GrpObj X where
  __ := hF.monObj X
  inv := hF.preimage ι[F.obj X]
  left_inv := hF.map_injective <| by
    simp [η_of_cartesianMonoidalCategory, CartesianMonoidalCategory.terminalComparison]
  right_inv := hF.map_injective <| by
    simp [η_of_cartesianMonoidalCategory, CartesianMonoidalCategory.terminalComparison]

omit [F.OplaxMonoidal] in

@[reassoc]
lemma map_braiding_hom_comp_δ [F.OplaxMonoidal] [BraidedCategory C] [BraidedCategory D]
    (X Y : C) :
    F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  ext <;> simp [← Functor.map_comp]

lemma isCommMonObj_of_fullyFaithful [BraidedCategory C] [BraidedCategory D] [MonObj (F.obj X)]
    [IsCommMonObj (F.obj X)] :
    letI := hF.monObj X; IsCommMonObj X := by
  letI := hF.monObj X
  refine ⟨hF.map_injective ?_⟩
  simp only [Functor.map_comp, FullyFaithful.monObj_mul, FullyFaithful.map_preimage]
  rw [map_braiding_hom_comp_δ_assoc, IsCommMonObj.mul_comm]

noncomputable def homMulEquivOfFullyFaithful [MonObj (F.obj X)] (Y : C) :
    letI := hF.monObj X; (Y ⟶ X) ≃* (F.obj Y ⟶ F.obj X) :=
  letI := hF.monObj X
  { hF.homEquiv with
    map_mul' := map_hom_mul F (map_mul_monObj F hF X) }

lemma homMulEquivOfFullyFaithful_apply [MonObj (F.obj X)] {Y : C} (f : Y ⟶ X) :
    homMulEquivOfFullyFaithful F hF X Y f = F.map f := rfl

lemma map_mul_of_fullyFaithful [MonObj (F.obj X)] {Y : C} (f g : Y ⟶ X) :
    letI := hF.monObj X; F.map (f * g) = F.map f * F.map g :=
  letI := hF.monObj X
  map_hom_mul F (map_mul_monObj F hF X) f g

lemma map_one_of_fullyFaithful [MonObj (F.obj X)] (Y : C) :
    letI := hF.monObj X; F.map (1 : Y ⟶ X) = 1 :=
  letI := hF.monObj X
  map_hom_one F (map_one_monObj F hF X) Y

omit [F.OplaxMonoidal] in

lemma mul_comp_ofIso_inv {M X' Y : D} [MonObj M] (e : M ≅ X') (f₁ f₂ : Y ⟶ X') :
    letI := MonObj.ofIso e; (f₁ * f₂) ≫ e.inv = (f₁ ≫ e.inv) * (f₂ ≫ e.inv) := by
  letI := MonObj.ofIso e
  exact MonObj.mul_comp f₁ f₂ e.inv

omit [F.OplaxMonoidal] in

lemma isCommMonObj_ofIso [BraidedCategory D] {M X' : D} [MonObj M] [IsCommMonObj M]
    (e : M ≅ X') : letI := MonObj.ofIso e; IsCommMonObj X' := by
  letI := MonObj.ofIso e
  refine ⟨?_⟩
  rw [MonObj.ofIso_mul, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]

omit [F.OplaxMonoidal] in
lemma one_comp_ofIso_inv {M X' Y : D} [MonObj M] (e : M ≅ X') :
    letI := MonObj.ofIso e; (1 : Y ⟶ X') ≫ e.inv = 1 := by
  letI := MonObj.ofIso e
  exact MonObj.one_comp e.inv

end epsilon

section delta

variable {R : Type u} [CommRing R] (G : Over (Spec (CommRingCat.of R)))

@[reducible] noncomputable def secAlgebra : Algebra R Γ(G.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop).hom.toAlgebra

attribute [local instance] secAlgebra

lemma algebraMap_sec_def :
    algebraMap R Γ(G.left, ⊤) = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop).hom :=
  rfl

lemma ofHom_algebraMap_sec :
    CommRingCat.ofHom (algebraMap R Γ(G.left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop :=
  rfl

lemma isAffine_left [IsAffineHom G.hom] : IsAffine G.left := isAffine_of_isAffineHom G.hom

lemma isoSpec_hom_comp_specMap_algebraMap [IsAffine G.left] :
    G.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(G.left, ⊤))) = G.hom := by
  rw [ofHom_algebraMap_sec, Spec.map_comp, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

noncomputable def overIsoSpec [IsAffine G.left] :
    G ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Γ(G.left, ⊤)))) :=
  Over.isoMk G.left.isoSpec (isoSpec_hom_comp_specMap_algebraMap G)

@[scoped simp] lemma overIsoSpec_hom_left [IsAffine G.left] :
    (overIsoSpec G).hom.left = G.left.toSpecΓ := rfl

@[scoped simp] lemma overIsoSpec_inv_left [IsAffine G.left] :
    (overIsoSpec G).inv.left = G.left.isoSpec.inv := by
  simp [overIsoSpec]

noncomputable def pointOfAlgHom [IsAffine G.left] {L : Type u} [CommRing L] [Algebra R L]
    (φ : Γ(G.left, ⊤) →ₐ[R] L) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ G.left.isoSpec.inv) (by
    simp only [Over.mk_left, Over.mk_hom, Category.assoc]
    rw [← isoSpec_hom_comp_specMap_algebraMap G, Iso.inv_hom_id_assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext φ.commutes)

@[scoped simp] lemma pointOfAlgHom_left [IsAffine G.left] {L : Type u} [CommRing L] [Algebra R L]
    (φ : Γ(G.left, ⊤) →ₐ[R] L) :
    (pointOfAlgHom G φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ G.left.isoSpec.inv :=
  rfl

end delta

section betaA

variable (R : Type u) [CommRing R]

noncomputable def specOver : (CommAlgCat.{u} R)ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) where
  obj A := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A.unop)))
  map {A B} f := Over.homMk (Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom)) (by
    show Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B.unop)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A.unop))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact f.unop.hom.commutes x)
  map_comp {A B C} f g := by
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (f ≫ g).unop.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.unop.hom.toRingHom)
    rw [← Spec.map_comp]
    rfl

lemma specOver_w {A B : (CommAlgCat.{u} R)ᵒᵖ} (h : (specOver R).obj A ⟶ (specOver R).obj B) :
    CommRingCat.ofHom (algebraMap R B.unop) ≫ Spec.preimage h.left =
      CommRingCat.ofHom (algebraMap R A.unop) := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage]
  exact Over.w h

noncomputable def specOverFullyFaithful : (specOver R).FullyFaithful where
  preimage {A B} h :=
    (CommAlgCat.ofHom
      { toRingHom := (Spec.preimage h.left).hom
        commutes' := fun r => by
          simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (specOver_w R h)) r }).op
  map_preimage {A B} h := by
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (Spec.preimage h.left).hom) = h.left
    rw [CommRingCat.ofHom_hom]
    exact Spec.map_preimage h.left
  preimage_map {A B} f := by
    apply Quiver.Hom.unop_inj
    ext x
    have h1 : Spec.preimage (Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom)) =
        CommRingCat.ofHom f.unop.hom.toRingHom := Spec.preimage_map _
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h1) x

@[scoped simp] lemma specOver_map_left {A B : (CommAlgCat.{u} R)ᵒᵖ} (f : A ⟶ B) :
    ((specOver R).map f).left = Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) := rfl

end betaA

section gamma

variable {R : Type u} [CommRing R]

section
variable (G : Over (Spec (CommRingCat.of R)))
attribute [local instance] secAlgebra

lemma secFiniteType [IsAffineHom G.hom] [LocallyOfFiniteType G.hom] : Algebra.FiniteType R Γ(G.left, ⊤) := by
  haveI := isAffine_left G
  rw [← RingHom.finiteType_algebraMap, algebraMap_sec_def, CommRingCat.hom_comp]
  have h1 : (G.hom.appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  exact h1.comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
end

open WithConv in

noncomputable def convHomMulEquiv' (A : (CommAlgCat.{u} R)ᵒᵖ) [MonObj A]
    (L : Type u) [CommRing L] [Algebra R L] :
    WithConv (A.unop →ₐ[R] L) ≃* (op (CommAlgCat.of R L) ⟶ A) where
  toFun φ := (show A.unop ⟶ CommAlgCat.of R L from CommAlgCat.ofHom φ.ofConv).op
  invFun f := toConv f.unop.hom
  left_inv φ := rfl
  right_inv f := rfl
  map_mul' φ ψ := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    ext c
    exact AlgHom.convMul_apply φ ψ c

@[scoped simp] lemma convHomMulEquiv'_apply_unop_hom (A : (CommAlgCat.{u} R)ᵒᵖ) [MonObj A]
    (L : Type u) [CommRing L] [Algebra R L] (φ : WithConv (A.unop →ₐ[R] L)) :
    (convHomMulEquiv' A L φ).unop.hom = φ.ofConv := rfl

end gamma

section assembly

variable {R : Type u} [CommRing R] (G : Over (Spec (CommRingCat.of R)))

attribute [local instance] secAlgebra

noncomputable scoped instance : (specOver R).OplaxMonoidal := .ofChosenFiniteProducts _

noncomputable abbrev ΓOp : (CommAlgCat.{u} R)ᵒᵖ := op (CommAlgCat.of R Γ(G.left, ⊤))

lemma specOver_obj_ΓOp :
    (specOver R).obj (ΓOp G) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Γ(G.left, ⊤)))) := rfl

variable [GrpObj G] [IsAffine G.left]

noncomputable scoped instance grpObjSpec : GrpObj ((specOver R).obj (ΓOp G)) :=
  GrpObj.ofIso (overIsoSpec G)

scoped instance isCommMonObjSpec [IsCommMonObj G] : IsCommMonObj ((specOver R).obj (ΓOp G)) :=
  isCommMonObj_ofIso (overIsoSpec G)

noncomputable scoped instance grpObjΓ : GrpObj (ΓOp G) :=
  grpObjOfFullyFaithful (specOver R) (specOverFullyFaithful R) (ΓOp G)

scoped instance isCommMonObjΓ [IsCommMonObj G] : IsCommMonObj (ΓOp G) :=
  isCommMonObj_of_fullyFaithful (specOver R) (specOverFullyFaithful R) (ΓOp G)

noncomputable scoped instance hopfΓ : HopfAlgebra R (ΓOp G).unop := hopfAlgebraUnop (ΓOp G)

noncomputable scoped instance (priority := high) algΓ : Algebra R (ΓOp G).unop := Bialgebra.toAlgebra

p2m_attr_erase "instance" "CommAlgCat.monObjOpOf"

variable (L : Type u) [CommRing L] [Algebra R L]

noncomputable def ptsEquiv :
    WithConv ((ΓOp G).unop →ₐ[R] L) ≃
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ G) :=
  (convHomMulEquiv' (ΓOp G) L).toEquiv.trans <|
    (specOverFullyFaithful R).homEquiv.trans
      { toFun := fun f => f ≫ (overIsoSpec G).inv
        invFun := fun f => f ≫ (overIsoSpec G).hom
        left_inv := fun f => (Category.assoc _ _ _).trans <|
          (congrArg (f ≫ ·) (overIsoSpec G).inv_hom_id).trans (Category.comp_id f)
        right_inv := fun f => (Category.assoc _ _ _).trans <|
          (congrArg (f ≫ ·) (overIsoSpec G).hom_inv_id).trans (Category.comp_id f) }

lemma ptsEquiv_apply (φ : WithConv ((ΓOp G).unop →ₐ[R] L)) :
    ptsEquiv G L φ = (specOver R).map (convHomMulEquiv' (ΓOp G) L φ) ≫ (overIsoSpec G).inv :=
  rfl

lemma ptsEquiv_left (φ : WithConv ((ΓOp G).unop →ₐ[R] L)) :
    (ptsEquiv G L φ).left =
      Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ G.left.isoSpec.inv := by
  rw [ptsEquiv_apply, Over.comp_left, overIsoSpec_inv_left]
  rfl

lemma ptsEquiv_mul (φ ψ : WithConv ((ΓOp G).unop →ₐ[R] L)) :
    ptsEquiv G L (φ * ψ) = ptsEquiv G L φ * ptsEquiv G L ψ := by
  have h1 : convHomMulEquiv' (ΓOp G) L (φ * ψ) =
      convHomMulEquiv' (ΓOp G) L φ * convHomMulEquiv' (ΓOp G) L ψ := map_mul _ φ ψ
  have h2 := map_mul_of_fullyFaithful (specOver R) (specOverFullyFaithful R) (ΓOp G)
    (convHomMulEquiv' (ΓOp G) L φ) (convHomMulEquiv' (ΓOp G) L ψ)
  rw [ptsEquiv_apply, ptsEquiv_apply, ptsEquiv_apply, h1]
  exact (congrArg (· ≫ (overIsoSpec G).inv) h2).trans (mul_comp_ofIso_inv (overIsoSpec G) _ _)

lemma ptsEquiv_natural (L' : Type u) [CommRing L'] [Algebra R L'] (g : L →ₐ[R] L')
    (φ : WithConv ((ΓOp G).unop →ₐ[R] L)) :
    (ptsEquiv G L' (.toConv (g.comp φ.ofConv))).left =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (ptsEquiv G L φ).left := by
  rw [ptsEquiv_left, ptsEquiv_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end assembly

end EF1nA4
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom.EF1nA4"

namespace FlatUpgrade
open EF1nA4
variable {R : Type u} [CommRing R] (G : Over (Spec (CommRingCat.of R)))
attribute [local instance] secAlgebra

theorem secModuleFlat [IsAffine G.left] [Flat G.hom] : Module.Flat R Γ(G.left, ⊤) := by
  have h2 : Flat (G.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(G.left,⊤)))) := by
    rw [isoSpec_hom_comp_specMap_algebraMap G]; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp
    ((MorphismProperty.cancel_left_of_respectsIso @Flat _ _).mp h2)

theorem flatΓ [GrpObj G] [IsCommMonObj G] [IsAffineHom G.hom] [Flat G.hom] :
    haveI : IsAffine G.left := isAffine_left G
    Module.Flat R (ΓOp G).unop := by
  haveI : IsAffine G.left := isAffine_left G
  exact secModuleFlat G

end FlatUpgrade
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom.EF1nA4"

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

p2m_attr_erase "instance" "CommAlgCat.monObjOpOf in"
open EF1nA4 FlatUpgrade NeronModelInfra GoodReductionJacobian in
set_option autoImplicit false in
set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    [IsAffineHom g] [Flat g] [LocallyOfFiniteType g] :
    letI : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra
    haveI : IsAffine A := isAffine_of_isAffineHom g
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Algebra.FiniteType R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ (iso : H ≃ₐ[R] Γ(A, ⊤))
        (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g),
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
          (e T φ).1 =
            Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso.symm : Γ(A, ⊤) →ₐ[R] H)).toRingHom)) ≫ A.isoSpec.inv) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          e T (φ * ψ) = L.mul _ (e T φ) (e T ψ)) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (σ : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          (e T' (.toConv (σ.comp φ.ofConv))).1 =
            Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e T φ).1) := by
  classical
  obtain ⟨gE, hmul, hone, hinv⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_eq L
  letI := gE
  haveI : IsCommMonObj (Over.mk g) := by
    refine ⟨?_⟩
    have key : ∀ (a b : (Over.mk g) ⊗ (Over.mk g) ⟶ Over.mk g),
        CartesianMonoidalCategory.lift a b ≫ MonObj.mul = CartesianMonoidalCategory.lift b a ≫ MonObj.mul := by
      intro a b
      apply (schemeHomOverEquivOverHom _ g).symm.injective
      change overHomToSchemeHomOver _ = overHomToSchemeHomOver _
      have h1 : overHomToSchemeHomOver (CartesianMonoidalCategory.lift a b ≫ MonObj.mul) =
          L.mul _ (overHomToSchemeHomOver a) (overHomToSchemeHomOver b) := hmul _ a b
      have h2 : overHomToSchemeHomOver (CartesianMonoidalCategory.lift b a ≫ MonObj.mul) =
          L.mul _ (overHomToSchemeHomOver b) (overHomToSchemeHomOver a) := hmul _ b a
      exact h1.trans ((hcomm _ _ _).trans h2.symm)
    have h := key (CartesianMonoidalCategory.snd _ _) (CartesianMonoidalCategory.fst _ _)
    rw [CartesianMonoidalCategory.lift_snd_fst, CartesianMonoidalCategory.lift_fst_snd, Category.id_comp] at h
    exact h
  haveI : IsAffineHom (Over.mk g).hom := by change IsAffineHom g; infer_instance
  haveI : Flat (Over.mk g).hom := by change Flat g; infer_instance
  haveI : LocallyOfFiniteType (Over.mk g).hom := by change LocallyOfFiniteType g; infer_instance
  haveI : IsAffine (Over.mk g).left := isAffine_left (Over.mk g)
  letI : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra

  let iso : (ΓOp (Over.mk g)).unop ≃ₐ[R] Γ(A, ⊤) := { (RingEquiv.refl _) with commutes' := fun r => rfl }
  refine ⟨(ΓOp (Over.mk g)).unop, inferInstance, hopfAlgebraUnop (ΓOp (Over.mk g)), secFiniteType (Over.mk g),
    flatΓ (Over.mk g), isCocommUnop (ΓOp (Over.mk g)), iso,
    fun T _ _ => (ptsEquiv (Over.mk g) T).trans (schemeHomOverEquivOverHom _ g).symm, ?_, ?_, ?_⟩
  · intro T _ _ φ
    change (overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T) φ)).1 = _
    rw [overHomToSchemeHomOver_coe, ptsEquiv_left]
    rfl
  · intro T _ _ φ ψ
    change overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T) (φ * ψ)) =
      L.mul _ (overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T) φ)) (overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T) ψ))
    rw [ptsEquiv_mul (Over.mk g) T φ ψ, ← hmul]
    congr 1
  · intro T T' _ _ _ _ σ φ
    change (overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T') (.toConv (σ.comp φ.ofConv)))).1 =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T) φ)).1
    rw [overHomToSchemeHomOver_coe, overHomToSchemeHomOver_coe]
    exact ptsEquiv_natural (Over.mk g) T T' σ φ

end S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom (solution)
