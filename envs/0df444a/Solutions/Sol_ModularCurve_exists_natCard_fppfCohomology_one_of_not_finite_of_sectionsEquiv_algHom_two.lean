-- Prove2me | solution 1 for ModularCurve.exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/faf44d65-329d-516a-9b48-f70df370c133

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GaloisRep_Flat
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.RingHom.Flat
import Definitions.Def_AlgebraicGeometry_FppfGmRepresentable
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Theorems.Thm_ModularCurve_exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two
import Theorems.Thm_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two
p2m_attr_erase "instance" "EtaleCohomologyLES.instAdditiveSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.instFullSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.constSchemeOpAdditive EtaleCohomologyLES.instFaithfulSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf AlgebraicGeometry.Scheme.instAdditiveSheafFppfSmallFppfTopologyAbFppfCohomologyFunctor EtaleCohomologyLES.idIsContinuousEtaleFppf EtaleCohomologyLES.constantSheafEtaleAdditive EtaleCohomologyLES.constantSheafFppfAdditive EtaleCohomologyLES.etaleTopologySubcanonical EtaleCohomologyLES.etaleSheavesIsGrothendieckAbelian"
p2m_attr_erase "simp" "FppfCohomologyLES.cohomologyDimensionShiftEquiv_apply EtaleCohomologyLES.sheafInclusionOfLe_obj_obj FppfCohomologyLES.homPostcompAddEquiv_apply EtaleCohomologyLES.fppfSheafToEtaleSheaf_obj_obj AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_inv_app_apply FppfCohomologyLES.homPostcompAddEquiv_symm_apply AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_hom_app_apply EtaleCohomologyLES.sheafInclusionOfLe_map_hom EtaleCohomologyLES.fppfSheafToEtaleSheaf_map_hom Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false

namespace ConvPoints

section ConvolutionGroup

p2m_open "Coalgebra Bialgebra HopfAlgebra WithConv TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct Algebra.TensorProduct"
open scoped Coalgebra
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open FppfRepresentableGroupSchemeSheaf

section ConvGroup

variable {R : Type} [CommSemiring R] {C : Type} [CommRing C] [HopfAlgebra R C]
  {A : Type} [CommRing A] [Algebra R A]

noncomputable def antipodeAlgHom : C →ₐ[R] C where
  toFun := antipode R
  map_one' := antipode_one
  map_mul' a b := by rw [antipode_mul]; exact mul_comm _ _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, antipode_one]

@[scoped simp] lemma antipodeAlgHom_apply (c : C) : antipodeAlgHom (R := R) c = antipode R c := rfl

private lemma algConvMul_apply (f g : WithConv (C →ₐ[R] A)) {c : C} {ι : Type*}
    (𝓡 : Coalgebra.Repr R c ι) :
    (f * g).ofConv c = ∑ i ∈ 𝓡.index, f.ofConv (𝓡.left i) * g.ofConv (𝓡.right i) := by
  have hb : (f * g).ofConv.toLinearMap
      = (toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap).ofConv := rfl
  have h := 𝓡.convMul_apply (toConv f.ofConv.toLinearMap) (toConv g.ofConv.toLinearMap)
  calc (f * g).ofConv c = (f * g).ofConv.toLinearMap c := rfl
    _ = (toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap) c := by rw [hb]
    _ = ∑ i ∈ 𝓡.index, f.ofConv (𝓡.left i) * g.ofConv (𝓡.right i) := h

lemma conv_inv_mul (f : WithConv (C →ₐ[R] A)) :
    toConv (f.ofConv.comp antipodeAlgHom) * f = 1 := by
  apply ofConv_injective
  apply AlgHom.ext
  intro c
  have 𝓡 := ℛ R c
  rw [show ((toConv (f.ofConv.comp antipodeAlgHom) * f).ofConv) c
      = ∑ i ∈ 𝓡.index, (f.ofConv.comp antipodeAlgHom) (𝓡.left i) * f.ofConv (𝓡.right i)
    from algConvMul_apply _ _ 𝓡]
  have hs := sum_antipode_mul_eq_algebraMap_counit (R := R) 𝓡
  calc ∑ i ∈ 𝓡.index, (f.ofConv.comp antipodeAlgHom) (𝓡.left i) * f.ofConv (𝓡.right i)
      = f.ofConv (∑ i ∈ 𝓡.index, antipode R (𝓡.left i) * 𝓡.right i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [AlgHom.comp_apply, antipodeAlgHom_apply, map_mul]
    _ = f.ofConv (algebraMap R C (counit c)) := by rw [hs]
    _ = algebraMap R A (counit c) := f.ofConv.commutes _
    _ = (1 : WithConv (C →ₐ[R] A)).ofConv c := rfl

noncomputable scoped instance instCommGroupWithConv [Coalgebra.IsCocomm R C] :
    CommGroup (WithConv (C →ₐ[R] A)) :=
  { (inferInstance : CommMonoid (WithConv (C →ₐ[R] A))) with
    inv := fun f => toConv (f.ofConv.comp antipodeAlgHom)
    inv_mul_cancel := conv_inv_mul }

theorem isCocomm_of_convMul_comm
    (h : ∀ f g : WithConv (C →ₐ[R] TensorProduct R C C), f * g = g * f) :
    Coalgebra.IsCocomm R C := by
  refine ⟨?_⟩
  ext c
  have 𝓡 := ℛ R c
  have h1 : (toConv (includeLeft : C →ₐ[R] TensorProduct R C C)
      * toConv (includeRight : C →ₐ[R] TensorProduct R C C)).ofConv c = comul c := by
    rw [algConvMul_apply _ _ 𝓡]
    calc ∑ i ∈ 𝓡.index,
          (includeLeft : C →ₐ[R] TensorProduct R C C) (𝓡.left i)
            * (includeRight : C →ₐ[R] TensorProduct R C C) (𝓡.right i)
        = ∑ i ∈ 𝓡.index, 𝓡.left i ⊗ₜ[R] 𝓡.right i := by
          exact Finset.sum_congr rfl fun i _ => by
            rw [includeLeft_apply, includeRight_apply, tmul_mul_tmul, mul_one, one_mul]
      _ = comul c := 𝓡.eq
  have h2 : (toConv (includeRight : C →ₐ[R] TensorProduct R C C)
      * toConv (includeLeft : C →ₐ[R] TensorProduct R C C)).ofConv c
      = TensorProduct.comm R C C (comul c) := by
    rw [algConvMul_apply _ _ 𝓡]
    calc ∑ i ∈ 𝓡.index,
          (includeRight : C →ₐ[R] TensorProduct R C C) (𝓡.left i)
            * (includeLeft : C →ₐ[R] TensorProduct R C C) (𝓡.right i)
        = ∑ i ∈ 𝓡.index, 𝓡.right i ⊗ₜ[R] 𝓡.left i := by
          exact Finset.sum_congr rfl fun i _ => by
            rw [includeLeft_apply, includeRight_apply, tmul_mul_tmul, mul_one, one_mul]
      _ = TensorProduct.comm R C C (comul c) := by rw [← 𝓡.eq, map_sum]; simp
  have hcomm := h (toConv (includeRight : C →ₐ[R] TensorProduct R C C))
    (toConv (includeLeft : C →ₐ[R] TensorProduct R C C))
  calc (TensorProduct.comm R C C) (comul c)
      = (toConv (includeRight : C →ₐ[R] TensorProduct R C C)
          * toConv (includeLeft : C →ₐ[R] TensorProduct R C C)).ofConv c := h2.symm
    _ = (toConv (includeLeft : C →ₐ[R] TensorProduct R C C)
          * toConv (includeRight : C →ₐ[R] TensorProduct R C C)).ofConv c := by rw [hcomm]
    _ = comul c := h1

noncomputable def compConvMonoidHom {B : Type} [CommRing B] [Algebra R B] (h : A →ₐ[R] B) :
    WithConv (C →ₐ[R] A) →* WithConv (C →ₐ[R] B) where
  toFun f := toConv (h.comp f.ofConv)
  map_one' := by
    apply ofConv_injective
    apply AlgHom.ext
    intro c
    show h ((1 : WithConv (C →ₐ[R] A)).ofConv c) = (1 : WithConv (C →ₐ[R] B)).ofConv c
    show h (algebraMap R A (counit c)) = algebraMap R B (counit c)
    exact h.commutes _
  map_mul' f g := by
    rw [h.comp_convMul_distrib f g, toConv_ofConv]

end ConvGroup

noncomputable def ringHomToAlgHom {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B] (g : A →+* B) : A →ₐ[ℤ] B :=
  { toRingHom := g
    commutes' := fun r => by
      have h1 : algebraMap ℤ A r = ((r : ℤ) : A) := by
        simp
      have h2 : algebraMap ℤ B r = ((r : ℤ) : B) := by
        simp
      rw [h1, h2]
      exact map_intCast g r }

def IsCocommW (R : Type) [CommSemiring R] (C : Type) [CommRing C] [HopfAlgebra R C] : Prop :=
  Coalgebra.IsCocomm R C

theorem IsCocommW.out {R : Type} [CommSemiring R] {C : Type} [CommRing C] [HopfAlgebra R C]
    (h : IsCocommW R C) : Coalgebra.IsCocomm R C := h

theorem IsCocommW.mk {R : Type} [CommSemiring R] {C : Type} [CommRing C] [HopfAlgebra R C]
    (h : Coalgebra.IsCocomm R C) : IsCocommW R C := h

end ConvolutionGroup

section Transport

p2m_open "Coalgebra Bialgebra HopfAlgebra WithConv TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

variable {R : Type} [CommSemiring R] {C : Type} [CommRing C] [HopfAlgebra R C]
  {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem convMul_comm_of_comp_injective (h : A →ₐ[R] B) (hinj : Function.Injective h)
    (hcomm : ∀ f g : WithConv (C →ₐ[R] B), f * g = g * f)
    (f g : WithConv (C →ₐ[R] A)) : f * g = g * f := by
  apply ofConv_injective
  apply AlgHom.ext
  intro c
  have h1 : (compConvMonoidHom (C := C) h) (f * g) = (compConvMonoidHom (C := C) h) (g * f) := by
    rw [map_mul, map_mul, hcomm]
  have h2 : h ((f * g).ofConv c) = h ((g * f).ofConv c) := by
    have := congrArg (fun (x : WithConv (C →ₐ[R] B)) => x.ofConv c) h1
    simpa [compConvMonoidHom] using this
  exact hinj h2

theorem mul_comm_of_addEquiv {M : Type*} {G : Type} [AddCommMonoid M] [Monoid G]
    (e : M ≃+ Additive G) (f g : G) : f * g = g * f := by
  have key : ∀ x y : Additive G, x + y = y + x := fun x y => by
    rw [← e.apply_symm_apply x, ← e.apply_symm_apply y, ← map_add, add_comm, map_add]
  have := key (Additive.ofMul f) (Additive.ofMul g)
  exact this

end Transport

section FppfObjects

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

section FppfOfFlatFiniteType

variable {R : Type} [CommRing R]

theorem fppfProperty_specMap_algebraMap [IsNoetherianRing R] (T : Type) [CommRing T]
    [Algebra R T] [Module.Flat R T] [Algebra.FiniteType R T] :
    fppfProperty (Spec.map (CommRingCat.ofHom (algebraMap R T))) := by
  refine ⟨?_, ?_⟩
  · exact (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance))

theorem finiteType_tensorProduct (A B : Type) [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B] :
    Algebra.FiniteType R (TensorProduct R A B) :=
  Algebra.FiniteType.trans (S := A) inferInstance inferInstance

theorem flat_tensorProduct (A B : Type) [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [Module.Flat R A] [Module.Flat R B] :
    Module.Flat R (TensorProduct R A B) :=
  inferInstance

theorem fppfProperty_specMap_algebraMap_tensorProduct [IsNoetherianRing R] (A B : Type)
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Flat R A] [Module.Flat R B]
    [Algebra.FiniteType R A] [Algebra.FiniteType R B] :
    fppfProperty (Spec.map (CommRingCat.ofHom (algebraMap R (TensorProduct R A B)))) :=
  haveI := finiteType_tensorProduct (R := R) A B
  fppfProperty_specMap_algebraMap (R := R) (TensorProduct R A B)

end FppfOfFlatFiniteType

end FppfObjects

section TensorSquareObject

p2m_open "Coalgebra Bialgebra HopfAlgebra WithConv TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

section TensorSquare

variable (R : Type) [CommRing R] (C : Type) [CommRing C] [HopfAlgebra R C]

noncomputable def tensorSquare : Type := TensorProduct R C C

noncomputable scoped instance : CommRing (tensorSquare R C) :=
  inferInstanceAs (CommRing (TensorProduct R C C))

noncomputable scoped instance : Algebra R (tensorSquare R C) :=
  inferInstanceAs (Algebra R (TensorProduct R C C))

theorem isCocomm_of_convMul_comm'
    (h : ∀ f g : WithConv (C →ₐ[R] tensorSquare R C), f * g = g * f) :
    Coalgebra.IsCocomm R C :=
  isCocomm_of_convMul_comm h

noncomputable def tensorSquareScheme : Scheme.{0} :=
  Spec (CommRingCat.of (tensorSquare R C))

noncomputable def tensorSquareHom : tensorSquareScheme R C ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (tensorSquare R C)))

theorem fppfProperty_tensorSquareHom [IsNoetherianRing R]
    (hfl : Module.Flat R C) (hft : Algebra.FiniteType R C) :
    fppfProperty (tensorSquareHom R C) :=
  haveI := hfl
  haveI := hft
  fppfProperty_specMap_algebraMap_tensorProduct (R := R) C C

end TensorSquare

section SiteMembership

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

noncomputable def tensorSquareFppf (hfl : AlgebraicGeometry.Flat (tensorSquareHom ℤ K))
    (hlfp : AlgebraicGeometry.LocallyOfFinitePresentation (tensorSquareHom ℤ K)) :
    specInt.Fppf :=
  haveI := hfl
  haveI := hlfp
  Scheme.Fppf.mk (tensorSquareHom ℤ K)

noncomputable def tensorSquareSections (hfl : AlgebraicGeometry.Flat (tensorSquareHom ℤ K))
    (hlfp : AlgebraicGeometry.LocallyOfFinitePresentation (tensorSquareHom ℤ K)) :
    tensorSquare ℤ K →ₐ[ℤ] Γ((tensorSquareFppf K hfl hlfp).left, ⊤) :=
  ringHomToAlgHom ((Scheme.ΓSpecIso (CommRingCat.of (tensorSquare ℤ K))).inv.hom)

theorem tensorSquareSections_injective (hfl : AlgebraicGeometry.Flat (tensorSquareHom ℤ K))
    (hlfp : AlgebraicGeometry.LocallyOfFinitePresentation (tensorSquareHom ℤ K)) :
    Function.Injective (tensorSquareSections K hfl hlfp) := by
  have h := ((Scheme.ΓSpecIso
    (CommRingCat.of (tensorSquare ℤ K))).symm.commRingCatIsoToRingEquiv).injective
  intro a b hab
  exact h hab

end SiteMembership

end TensorSquareObject

section Discharge

p2m_open "Coalgebra Bialgebra HopfAlgebra WithConv TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

theorem flat_int_transfer {N : Type} [AddCommMonoid N] {m₁ m₂ : Module ℤ N}
    (h : @Module.Flat ℤ N _ _ m₁) : @Module.Flat ℤ N _ _ m₂ := by
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact h

theorem finiteType_int_transfer {A : Type} [CommRing A] {a₁ a₂ : Algebra ℤ A}
    (h : @Algebra.FiniteType ℤ A _ _ a₁) : @Algebra.FiniteType ℤ A _ _ a₂ := by
  obtain rfl : a₁ = a₂ := Subsingleton.elim _ _
  exact h

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

theorem isCocommW_of_sectionsEquiv [hft : Algebra.FiniteType ℤ K] [hfl : Module.Flat ℤ K]
    (M : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      M.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤)))) :
    IsCocommW ℤ K := by
  have hfp : fppfProperty (tensorSquareHom ℤ K) :=
    fppfProperty_tensorSquareHom ℤ K (flat_int_transfer hfl) (finiteType_int_transfer hft)
  exact IsCocommW.mk (isCocomm_of_convMul_comm' ℤ K (fun f g =>
    convMul_comm_of_comp_injective (tensorSquareSections K hfp.1 hfp.2)
      (tensorSquareSections_injective K hfp.1 hfp.2)
      (mul_comm_of_addEquiv (e (tensorSquareFppf K hfp.1 hfp.2))) f g))

end Discharge

section Avatar

p2m_open "Coalgebra Bialgebra HopfAlgebra WithConv TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct Algebra.TensorProduct"
open scoped Coalgebra
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open FppfRepresentableGroupSchemeSheaf

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

noncomputable def pointsPre : Scheme.{0}ᵒᵖ ⥤ Type 0 :=
  Scheme.Γ.{0}.rightOp.op ⋙ yoneda.obj (op (CommRingCat.of K))

noncomputable def pointsPreRepresentableBy :
    (pointsPre K).RepresentableBy (Spec (CommRingCat.of K)) :=
  ΓSpec.adjunction.representableBy (op (CommRingCat.of K))

noncomputable def bundledAlgEquiv (R : CommRingCat.{0}) :
    (CommRingCat.of K ⟶ R) ≃ (K →ₐ[ℤ] ↑R) where
  toFun g := ringHomToAlgHom g.hom
  invFun φ := CommRingCat.ofHom φ.toRingHom
  left_inv _ := rfl
  right_inv _ := rfl

section Geom

variable (ic : IsCocommW ℤ K)

noncomputable def pointsAb : Scheme.{0}ᵒᵖ ⥤ Ab.{0} where
  obj T :=
    haveI := ic.out
    AddCommGrpCat.of (Additive (WithConv (K →ₐ[ℤ] Γ(T.unop, ⊤))))
  map {T T'} φ :=
    haveI := ic.out
    AddCommGrpCat.ofHom
      (MonoidHom.toAdditive (compConvMonoidHom (C := K) (ringHomToAlgHom φ.unop.appTop.hom)))
  map_id T := by
    haveI := ic.out
    refine AddCommGrpCat.hom_ext ?_
    refine AddMonoidHom.ext fun s => ?_
    refine congrArg Additive.ofMul (ofConv_injective ?_)
    refine AlgHom.ext fun c => ?_
    show (𝟙 T.unop : T.unop ⟶ T.unop).appTop.hom ((Additive.toMul s).ofConv c)
      = (Additive.toMul s).ofConv c
    simp
  map_comp {T T' T''} φ ψ := by
    haveI := ic.out
    refine AddCommGrpCat.hom_ext ?_
    refine AddMonoidHom.ext fun s => ?_
    refine congrArg Additive.ofMul (ofConv_injective ?_)
    refine AlgHom.ext fun c => ?_
    show ((φ ≫ ψ).unop.appTop.hom) ((Additive.toMul s).ofConv c)
      = (ψ.unop.appTop.hom) ((φ.unop.appTop.hom) ((Additive.toMul s).ofConv c))
    simp

def algHomAdditiveEquiv (A : Type) [CommRing A] [Algebra ℤ A] :
    (K →ₐ[ℤ] A) ≃ Additive (WithConv (K →ₐ[ℤ] A)) where
  toFun f := Additive.ofMul (toConv f)
  invFun s := (Additive.toMul s).ofConv
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def pointsAbForgetRepresentableBy :
    (pointsAb K ic ⋙ forget Ab).RepresentableBy (Spec (CommRingCat.of K)) where
  homEquiv {T} :=
    (((pointsPreRepresentableBy K).homEquiv.trans
      (CategoryTheory.opEquiv (op (Scheme.Γ.obj (op T))) (op (CommRingCat.of K)))).trans
      (bundledAlgEquiv K (Scheme.Γ.obj (op T)))).trans
      (algHomAdditiveEquiv K (Scheme.Γ.obj (op T)))
  homEquiv_comp {T T'} f g := by
    have h := (pointsPreRepresentableBy K).homEquiv_comp f g
    simp only [Equiv.trans_apply]
    rw [h]
    rfl

theorem isSheaf_pointsAb : Presheaf.IsSheaf Scheme.fppfTopology.{0} (pointsAb K ic) := by
  have : (pointsAb K ic ⋙ forget Ab).IsRepresentable :=
    (pointsAbForgetRepresentableBy K ic).isRepresentable
  exact isSheaf_fppf_ab_of_forget_isRepresentable _

noncomputable def avatarAb : Sheaf Scheme.fppfTopology.{0} Ab.{0} :=
  ⟨pointsAb K ic, isSheaf_pointsAb K ic⟩

noncomputable def avatar : Sheaf Scheme.fppfTopology.{0} Ab.{1} :=
  FppfKummerSES.sheafULift.obj (avatarAb K ic)

noncomputable def avatarSectionsEquiv (T : Scheme.{0}) :
    (avatar K ic).obj.obj (op T) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))) :=
  haveI := ic.out
  show ULift.{1} (Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤)))) ≃+
      Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))) from
    AddEquiv.ulift

theorem avatarSectionsEquiv_naturality {T T' : Scheme.{0}} (g : T ⟶ T')
    (s : (avatar K ic).obj.obj (op T')) (k : K) :
    (Additive.toMul (avatarSectionsEquiv K ic T ((avatar K ic).obj.map g.op s))) k
      = (Scheme.Γ.map g.op) ((Additive.toMul (avatarSectionsEquiv K ic T' s)) k) :=
  rfl

end Geom

end Avatar

section RestrictionIso

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

section MIso

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

theorem points_ext {A : Type} [CommRing A] {x y : Additive (WithConv (K →ₐ[ℤ] A))}
    (h : ∀ k : K, (Additive.toMul x) k = (Additive.toMul y) k) : x = y :=
  Additive.toMul.injective (WithConv.ext (AlgHom.ext h))

variable (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
  (eb : ∀ T : Scheme.{0}, X.obj.obj (op T) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))))
  (ebnat : ∀ {T T' : Scheme.{0}} (g : T ⟶ T') (s : X.obj.obj (op T')) (k : K),
    (Additive.toMul (eb T (X.obj.map g.op s))) k
      = (Scheme.Γ.map g.op) ((Additive.toMul (eb T' s)) k))
  (M : Sheaf (smallFppfTopology specInt) Ab.{1})
  (e : ∀ U : specInt.Fppf,
    M.1.obj (op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
  (enat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : M.1.obj (op V)) (k : K),
    (Additive.toMul (e U (M.1.map f.op s))) k
      = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))

noncomputable def isoRestrictionApp (U : specInt.Fppf) :
    M.1.obj (op U) ≅ X.obj.obj (op U.left) :=
  AddEquiv.toAddCommGrpIso ((e U).trans (eb U.left).symm)

include ebnat enat in
theorem isoRestrictionApp_naturality {U V : specInt.Fppf} (f : U ⟶ V) (s : M.1.obj (op V)) :
    (isoRestrictionApp K X eb M e U).hom (M.1.map f.op s) =
      X.obj.map f.left.op ((isoRestrictionApp K X eb M e V).hom s) := by
  change (eb U.left).symm (e U (M.1.map f.op s)) = X.obj.map f.left.op ((eb V.left).symm (e V s))
  apply (eb U.left).injective
  rw [AddEquiv.apply_symm_apply]
  apply points_ext K
  intro k
  rw [enat, ebnat, AddEquiv.apply_symm_apply]

include ebnat enat in

theorem nonempty_iso_restriction :
    Nonempty (M.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj) :=
  ⟨NatIso.ofComponents (fun U => isoRestrictionApp K X eb M e U.unop) (by
    intro U V f
    ext s
    exact isoRestrictionApp_naturality K X eb ebnat M e enat f.unop s)⟩

end MIso

end RestrictionIso

end ConvPoints
p2m_reactivate "P2MW.S_ModularCurve_exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two.ConvPoints"

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem solution
    (p : ℕ)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (M : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      M.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (enat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : M.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (M.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (a : ℕ) (ha : Nat.card (K →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a)
    (hK : ¬ Module.Finite ℤ K) :
    ∃ l1 : ℕ, Nat.card (fppfCohomology specInt M 1) = 2 ^ l1 ∧ l1 + a ≤ 1 := by
  have ic : ConvPoints.IsCocommW ℤ K := ConvPoints.isCocommW_of_sectionsEquiv K M e
  obtain ⟨l1, hX, hl⟩ :=
    ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two p K
      (ConvPoints.avatar K ic) (ConvPoints.avatarSectionsEquiv K ic)
      (ConvPoints.avatarSectionsEquiv_naturality K ic) hff hgen a ha hK
  obtain ⟨i⟩ := ConvPoints.nonempty_iso_restriction K (ConvPoints.avatar K ic)
    (ConvPoints.avatarSectionsEquiv K ic) (ConvPoints.avatarSectionsEquiv_naturality K ic) M e enat
  exact ⟨l1, (AlgebraicGeometry.natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
    (ConvPoints.avatar K ic) M i).trans hX, hl⟩

end S_ModularCurve_exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two
end P2MW
export P2MW.S_ModularCurve_exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two (solution)
