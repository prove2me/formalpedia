-- Prove2me | solution 1 for GoodReductionJacobian.nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f28dcb26-414d-5b7b-8af9-f1ff37914bc0

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GPIHost

open GoodReductionJacobian

section OfIso

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  {f' : A' ⟶ Spec (CommRingCat.of R)} (e : A' ≅ A) (he : e.hom ≫ f = f')

def fwd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f') : SchemeHomOver t f :=
  ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩

def bwd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨y.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc, y.2]⟩

@[scoped simp] theorem fwd_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f') :
    (fwd e he x).1 = x.1 ≫ e.hom := rfl
@[scoped simp] theorem bwd_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t f) :
    (bwd e he y).1 = y.1 ≫ e.inv := rfl

@[scoped simp] theorem fwd_bwd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t f) :
    fwd e he (bwd e he y) = y := Subtype.ext (by simp)
@[scoped simp] theorem bwd_fwd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f') :
    bwd e he (fwd e he x) = x := Subtype.ext (by simp)

theorem fwd_schemeHomOverComp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f') :
    fwd e he (schemeHomOverComp ψ hψ x) = schemeHomOverComp ψ hψ (fwd e he x) :=
  Subtype.ext (by simp)

def ofIso (G : RelativeGroupLaw R f) : RelativeGroupLaw R f' where
  mul t x y := bwd e he (G.mul t (fwd e he x) (fwd e he y))
  one t := bwd e he (G.one t)
  inv t x := bwd e he (G.inv t (fwd e he x))
  mul_assoc t x y z := by simp only [fwd_bwd, G.mul_assoc]
  one_mul t x := by simp only [fwd_bwd, G.one_mul, bwd_fwd]
  mul_one t x := by simp only [fwd_bwd, G.mul_one, bwd_fwd]
  inv_mul_cancel t x := by simp only [fwd_bwd, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, bwd_coe]
    have h := congrArg Subtype.val (G.mul_natural t t' ψ hψ (fwd e he x) (fwd e he y))
    simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h
    rw [fwd_schemeHomOverComp, fwd_schemeHomOverComp, ← h, Category.assoc]

end OfIso

theorem exists_isAlgClosed_ringHom_comp_eq {S : Type u} [CommRing S] (p : Ideal S) [hp : p.IsPrime]
    (k : Type u) [Field k] (x : S →+* k) (hx : RingHom.ker x = p)
    (k' : Type u) [Field k'] (x' : S →+* k') (hx' : RingHom.ker x' = p) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (ι : k →+* Ω) (ι' : k' →+* Ω), ι.comp x = ι'.comp x' := by
  let D := S ⧸ p
  let xD : D →+* k := Ideal.Quotient.lift p x (fun a ha => by rw [← RingHom.mem_ker, hx]; exact ha)
  let xD' : D →+* k' := Ideal.Quotient.lift p x' (fun a ha => by rw [← RingHom.mem_ker, hx']; exact ha)
  have hxD : Function.Injective xD := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hx] at ha
    rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]; exact ha
  have hxD' : Function.Injective xD' := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hx'] at ha
    rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]; exact ha
  letI : Algebra D k := xD.toAlgebra
  letI : Algebra D k' := xD'.toAlgebra
  haveI : Nontrivial (TensorProduct D k k') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain D k k' hxD hxD'
  obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal (TensorProduct D k k')
  letI : Field (TensorProduct D k k' ⧸ 𝔫) := Ideal.Quotient.field 𝔫
  let Ω := AlgebraicClosure (TensorProduct D k k' ⧸ 𝔫)
  let q : TensorProduct D k k' →+* Ω := (algebraMap _ Ω).comp (Ideal.Quotient.mk 𝔫)
  refine ⟨Ω, inferInstance, inferInstance, q.comp Algebra.TensorProduct.includeLeftRingHom,
    q.comp (Algebra.TensorProduct.includeRight (R := D) (A := k) (B := k')).toRingHom, ?_⟩
  ext a
  show q (Algebra.TensorProduct.includeLeftRingHom (x a)) = q (Algebra.TensorProduct.includeRight (x' a))
  congr 1
  have h1 : x a = algebraMap D k (Ideal.Quotient.mk p a) := (Ideal.Quotient.lift_mk p x _).symm
  have h2 : x' a = algebraMap D k' (Ideal.Quotient.mk p a) := (Ideal.Quotient.lift_mk p x' _).symm
  rw [h1, h2]
  show algebraMap D k (Ideal.Quotient.mk p a) ⊗ₜ[D] (1 : k') = (1 : k) ⊗ₜ[D] algebraMap D k' (Ideal.Quotient.mk p a)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]

end GPIHost
p2m_reactivate "P2MW.S_GoodReductionJacobian_nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq.GPIHost"

namespace GPIHost

open GoodReductionJacobian

theorem exists_algHom_of_finiteType {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Nontrivial A] : Nonempty (A →ₐ[k] k) := by
  obtain ⟨n, hn⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ n) := Ideal.Quotient.field n
  haveI : Module.Finite k (A ⧸ n) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ n)
  haveI : Algebra.IsIntegral k (A ⧸ n) := Algebra.IsIntegral.of_finite k (A ⧸ n)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ n)
  let e : k ≃ₐ[k] (A ⧸ n) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ n)) hb
  exact ⟨(e.symm : (A ⧸ n) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k n)⟩

theorem locallyOfFinitePresentation_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g] : LocallyOfFinitePresentation g := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of K), U.1) := IsLocallyNoetherian.component_noetherian U
  exact RingHom.FinitePresentation.of_finiteType.mp (HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance U V e)

theorem main
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (s : ↥(Spec (CommRingCat.of S)))
    (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k) (hx : RingHom.ker x = s.asIdeal)
    (k' : Type u) [Field k'] [IsAlgClosed k'] (x' : S →+* k') (hx' : RingHom.ker x' = s.asIdeal)
    (h : Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))) :
    Nonempty (RelativeGroupLaw k' (pullback.snd f (Spec.map (CommRingCat.ofHom x')))) := by
  classical

  obtain ⟨N, ιP, hci, hcomp⟩ := hproj
  haveI : IsProper f := by rw [← hcomp]; infer_instance

  obtain ⟨Ω, _, _, ι, ι', hιι⟩ := exists_isAlgClosed_ringHom_comp_eq s.asIdeal k x hx k' x' hx'
  obtain ⟨G⟩ := h

  set gx : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom x) with hgx
  set gx' : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom x') with hgx'
  set hι : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom ι) with hhι
  set hι' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k') := Spec.map (CommRingCat.ofHom ι') with hhι'
  have hcomp' : hι ≫ gx = hι' ≫ gx' := by
    rw [hhι, hgx, hhι', hgx', ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hιι]

  let GΩ : RelativeGroupLaw Ω (pullback.snd (pullback.snd f gx) hι) := G.baseChange hι

  let e : pullback (pullback.snd f gx') hι' ≅ pullback (pullback.snd f gx) hι :=
    pullbackLeftPullbackSndIso f gx' hι' ≪≫ pullback.congrHom rfl hcomp'.symm ≪≫ (pullbackLeftPullbackSndIso f gx hι).symm
  have he : e.hom ≫ pullback.snd (pullback.snd f gx) hι = pullback.snd (pullback.snd f gx') hι' := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  letI : Algebra k' Ω := ι'.toAlgebra
  let GΩ' : RelativeGroupLaw Ω (pullback.snd (pullback.snd f gx') (Spec.map (CommRingCat.ofHom (algebraMap k' Ω)))) :=
    ofIso e he GΩ

  haveI : LocallyOfFinitePresentation (pullback.snd f gx') := locallyOfFinitePresentation_of_field _
  obtain ⟨T, hTfg, -, Lₜ, -, -, -, -, -, -⟩ :=
    RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
      (pullback.snd f gx') GΩ' ∅

  haveI : Algebra.FiniteType k' T := (Subalgebra.fg_iff_finiteType T).mp hTfg
  obtain ⟨χ⟩ := exists_algHom_of_finiteType (k := k') (A := T)

  let Lχ := Lₜ.baseChange (Spec.map (CommRingCat.ofHom χ.toRingHom))
  have hχ0 : χ.toRingHom.comp (algebraMap k' T) = RingHom.id k' := RingHom.ext (fun a => χ.commutes a)
  have hχ1 : Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k' T)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hχ0, CommRingCat.ofHom_id, Spec.map_id]
  let e₃ : pullback (pullback.snd (pullback.snd f gx') (Spec.map (CommRingCat.ofHom (algebraMap k' T))))
      (Spec.map (CommRingCat.ofHom χ.toRingHom)) ≅ pullback f gx' :=
    pullbackLeftPullbackSndIso (pullback.snd f gx') _ _ ≪≫ pullback.congrHom rfl hχ1 ≪≫
      asIso (pullback.fst (pullback.snd f gx') (𝟙 _))
  have he₃ : e₃.symm.hom ≫ pullback.snd (pullback.snd (pullback.snd f gx') (Spec.map (CommRingCat.ofHom (algebraMap k' T))))
      (Spec.map (CommRingCat.ofHom χ.toRingHom)) = pullback.snd f gx' := by
    rw [Iso.symm_hom, Iso.inv_comp_eq]
    simp only [e₃, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [pullback.condition, Category.comp_id, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_snd]
  exact ⟨ofIso e₃.symm he₃ Lχ⟩

end GPIHost
p2m_reactivate "P2MW.S_GoodReductionJacobian_nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq.GPIHost"

theorem solution
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (s : ↥(Spec (CommRingCat.of S)))
    (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k) (hx : RingHom.ker x = s.asIdeal)
    (k' : Type u) [Field k'] [IsAlgClosed k'] (x' : S →+* k') (hx' : RingHom.ker x' = s.asIdeal)
    (h : Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))) :
    Nonempty (RelativeGroupLaw k' (pullback.snd f (Spec.map (CommRingCat.ofHom x')))) :=
  GPIHost.main f hproj s k x hx k' x' hx' h

end S_GoodReductionJacobian_nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq
end P2MW
export P2MW.S_GoodReductionJacobian_nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq (solution)
