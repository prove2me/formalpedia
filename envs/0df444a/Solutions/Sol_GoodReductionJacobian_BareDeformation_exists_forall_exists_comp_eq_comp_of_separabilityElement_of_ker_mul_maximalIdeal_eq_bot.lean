-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2c2ab871-6b8a-5298-ab8c-f32d876b1ebe

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_unit_chart_frame_bare
import Theorems.Thm_CerednikDrinfeld_QM_exists_injective_range_iff_isTangentVector
import Theorems.Thm_CerednikDrinfeld_QM_exists_pointDerivations_linearEquiv_tensor_of_isTangentVector
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_cls_one_endo_linearMap_pinned_unitPullback
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_chart_lift_comp_eq_of_isRegluingBy_bare
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_isTangentCoordsOfPairAt_bare
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_specialFibre_act_comp_eq_of_act_bare
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
import Theorems.Thm_CerednikDrinfeld_QM_exists_ringHom_moduleEnd_forall_eq_pushPt
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback
import Theorems.Thm_IsLocalRing_exists_separabilityElement_residueField_tensor_of_separabilityElement
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

universe u

namespace P2mCore

theorem specMap_comp_one {S' : Type} [CommRing S'] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S')} {Lₛ : RelativeGroupLaw S' fₛ}
    {B : Type} [CommRing B] [Algebra B S'] (D : GoodReductionJacobian.BareDeformation fₛ Lₛ B) :
    Spec.map (CommRingCat.ofHom (algebraMap B S')) ≫ (D.L.one (𝟙 _)).1 = (Lₛ.one (𝟙 _)).1 ≫ D.g := by
  have hx := D.hom (𝟙 _) (Lₛ.one (𝟙 _)) (Lₛ.one (𝟙 _))
  rw [Lₛ.one_mul] at hx
  letI := D.L.pointGroup (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B S')))
  set x : SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B S'))) D.f :=
    ⟨(Lₛ.one (𝟙 _)).1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, (Lₛ.one (𝟙 _)).2]⟩ with hxdef
  have hxx : x * x = x := Subtype.ext hx.symm
  have hx1 : x = 1 := mul_eq_left.1 hxx
  have hone : (D.L.one (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B S')))).1 =
      Spec.map (CommRingCat.ofHom (algebraMap B S')) ≫ (D.L.one (𝟙 _)).1 := by
    rw [← D.L.one_natural (𝟙 _) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B S')))
      (Spec.map (CommRingCat.ofHom (algebraMap B S'))) (by simp)]
    rfl
  rw [← hone]
  exact congrArg Subtype.val hx1.symm

theorem exists_pointDerivations_codRestrict {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] (ev : A →+* k)
    {W M : Type} [AddCommGroup W] [Module k W] [AddCommGroup M] [Module k M] (N : Submodule k M)
    (c : ↥(Algebra.PointDerivations k A ev (W →ₗ[k] M))) (hc : ∀ (a : A) (w : W), c.1 a w ∈ N) :
    ∃ ĉ : ↥(Algebra.PointDerivations k A ev (W →ₗ[k] ↥N)), ∀ (a : A) (w : W), ((ĉ.1 a w).1 : M) = c.1 a w := by
  let F : A →ₗ[k] (W →ₗ[k] ↥N) :=
    { toFun := fun a => LinearMap.codRestrict N (c.1 a) (hc a)
      map_add' := fun a b => by ext w; simp
      map_smul' := fun r a => by ext w; simp }
  refine ⟨⟨F, fun a b => ?_⟩, fun a w => rfl⟩
  ext w
  have := congrArg (fun (L : W →ₗ[k] M) => L w) (c.2 a b)
  simpa [F] using this

end P2mCore

open P2mCore in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 32000000 in
theorem solution
    (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (ResidueField S)]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField S) ℓ]
    [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    (hsmall : RingHom.ker (algebraMap S S₀) * maximalIdeal S = ⊥)
    {Λ : Type} [Ring Λ]
    (e : (S ⊗[ℤ] Λ) ⊗[S] (S ⊗[ℤ] Λ)) (he₁ : LinearMap.mul' S (S ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : S ⊗[ℤ] Λ, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
      TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e)
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)} (L₀ : RelativeGroupLaw S₀ f₀)
    (hL₀ : L₀.IsCommutative) (h₀ : AbelianSchemePropertyBundle S₀ f₀)
    (act₀ : Λ → (A₀ ⟶ A₀)) (act₀_over : ∀ x : Λ, act₀ x ≫ f₀ = f₀)
    (act₀_hom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ act₀ x =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨Q.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, Q.2]⟩).1)
    (act₀_one : act₀ 1 = 𝟙 A₀)
    (act₀_mul : ∀ x y : Λ, act₀ (x * y) = act₀ y ≫ act₀ x)
    (act₀_add : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t f₀),
      P.1 ≫ act₀ (x + y) =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨P.1 ≫ act₀ y, by rw [Category.assoc, act₀_over, P.2]⟩).1)
    (D₀ : BareDeformation f₀ L₀ S) :
    ∃ D : BareDeformation f₀ L₀ S,
      ∀ x : Λ, ∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ act₀ x ≫ D.g = D.g ≫ φ := by
  classical

  rcases subsingleton_or_nontrivial S₀ with h0 | h0
  · haveI : Subsingleton ↑(CommRingCat.of S₀) := h0
    haveI : IsEmpty ↥(Spec (CommRingCat.of S₀)) := (inferInstance : IsEmpty (PrimeSpectrum S₀))
    haveI : IsEmpty ↥A₀ := ⟨fun a => IsEmpty.false (f₀.base a)⟩
    exact ⟨D₀, fun x => ⟨𝟙 _, by simp, (AlgebraicGeometry.isInitialOfIsEmpty (X := A₀)).hom_ext _ _⟩⟩
  have hI : RingHom.ker (algebraMap S S₀) ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  haveI : IsProper D₀.f := D₀.bundle.proper
  haveI : Smooth D₀.f := D₀.bundle.smooth
  haveI : IsSeparated D₀.f := inferInstance

  obtain ⟨V, iV1, iV2, iV3, iV4, iV5, iV6, iV7, ιV, hι, hιI⟩ :=
    IsLocalRing.exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot (algebraMap S S₀) hsmall

  obtain ⟨𝒰, i₀, eu₀, heu₀, eu₁, heu₁, hU, -, -, -⟩ :=
    GoodReductionJacobian.BareDeformation.exists_orderedAffineCover_unit_chart_frame_bare S S₀ f₀ L₀ D₀
  letI instUe := algebraOfHom (pullback.snd D₀.f (specMap S (ResidueField S))) ((𝒰.baseChange D₀.f (ResidueField S)).U i₀)

  have hCF : ∀ (n : ℕ) (s : 𝒰.Idx n), _ := fun n s =>
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter D₀.f 𝒰 (ResidueField S) s
  choose σA hσA using hCF

  have hspec : specMap S (ResidueField S) = Spec.map (CommRingCat.ofHom (residue S)) := by
    show Spec.map (CommRingCat.ofHom (algebraMap S (ResidueField S))) = _
    rw [IsLocalRing.ResidueField.algebraMap_eq]
  have hak0 : IsPullback (pullback.fst D₀.f (specMap S (ResidueField S))) (pullback.snd D₀.f (specMap S (ResidueField S))) D₀.f (Spec.map (CommRingCat.ofHom (residue S))) := by
    rw [← hspec]; exact IsPullback.of_hasPullback _ _
  have hAk : AbelianSchemePropertyBundle (ResidueField S) (pullback.snd D₀.f (specMap S (ResidueField S))) :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback D₀.bundle (IsPullback.of_hasPullback D₀.f (specMap S (ResidueField S)))

  obtain ⟨W, iW1, iW2, τW, hWinj, hWrange, hWadd, hWsmul⟩ :=
    CerednikDrinfeld.QM.exists_injective_range_iff_isTangentVector (RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L) (ResidueField S) (RingHom.id (ResidueField S))

  haveI : LocallyOfFiniteType (pullback.snd D₀.f (specMap S (ResidueField S))) := inferInstance
  obtain ⟨Φ, hΦnat, hΦpin⟩ :=
    CerednikDrinfeld.QM.exists_pointDerivations_linearEquiv_tensor_of_isTangentVector (ResidueField S) (pullback.snd D₀.f (specMap S (ResidueField S))) (RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L) ((𝒰.baseChange D₀.f (ResidueField S)).U i₀) hU eu₁ heu₁ W τW hWinj hWrange hWadd hWsmul

  obtain ⟨H₁, j1, j2, j3, j4, cls₁, ρ, hcls₁, hcls₁0, hρid, hρcomp, hρadd, hρpin⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_cls_one_endo_linearMap_pinned_unitPullback (ResidueField S) (pullback.snd D₀.f (specMap S (ResidueField S))) (RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L) hAk (𝒰.baseChange D₀.f (ResidueField S))

  obtain ⟨jκ, hjκ, ψ, hψ, hψ₁, hψhom, hψone, hψmul, hψadd⟩ :=
    GoodReductionJacobian.BareDeformation.exists_specialFibre_act_comp_eq_of_act_bare S S₀ hπ hI L₀ act₀ act₀_over act₀_hom act₀_one act₀_mul act₀_add D₀

  have hkerle : RingHom.ker (algebraMap S S₀) ≤ RingHom.ker (residue S) := by rw [IsLocalRing.ker_residue]; exact hI
  set ρS : S₀ →+* (ResidueField S) := (algebraMap S S₀).liftOfSurjective hπ ⟨residue S, hkerle⟩ with hρS
  have hρScomp : ρS.comp (algebraMap S S₀) = residue S := RingHom.liftOfSurjective_comp _ hπ ⟨residue S, hkerle⟩
  have hrs : Spec.map (CommRingCat.ofHom ρS) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)) = Spec.map (CommRingCat.ofHom (residue S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρScomp]
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S S₀))) := IsClosedImmersion.spec_of_surjective _ hπ
  have hjf : jκ ≫ f₀ = (pullback.snd D₀.f (specMap S (ResidueField S))) ≫ Spec.map (CommRingCat.ofHom ρS) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap S S₀))), Category.assoc, Category.assoc, hrs, ← D₀.cart.w, ← Category.assoc, hjκ]
    exact hak0.w
  have hakA : IsPullback jκ (pullback.snd D₀.f (specMap S (ResidueField S))) f₀ (Spec.map (CommRingCat.ofHom ρS)) := by
    refine IsPullback.of_right ?_ hjf D₀.cart
    rw [hjκ, hrs]; exact hak0

  have hreg : D₀.IsRegluingBy 𝒰 (fun s => Iso.refl _) D₀ := by
    refine ⟨fun s => by simp, fun s => by simp, fun i => (𝒰.U i).ι, fun i => inferInstance, fun i => rfl, ?_, fun i => (morphismRestrict_ι _ _), fun s => by simp⟩
    intro x
    have hx : x ∈ (⨆ i, 𝒰.U i) := by rw [𝒰.iSup_eq_top]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  have hlifts : ∀ x : Λ, ∃ mx : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A,
      (∀ i, mx i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f) ∧ (∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mx i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ act₀ x ≫ D₀.g) := by
    intro x
    have h := GoodReductionJacobian.BareDeformation.exists_chart_lift_comp_eq_of_isRegluingBy_bare S S₀ hπ hker hsmall f₀ L₀ hL₀ h₀ hI V ιV hι hιI D₀ 𝒰 i₀ eu₀ heu₀ eu₁ heu₁ (fun s => σA 1 s) (fun s x => (hσA 1 s).1 x) (fun s a => (hσA 1 s).2 a) (fun s => Iso.refl _) D₀ hreg hU (act₀ x) (act₀_over x) jκ hjκ
    choose mx hmx using h
    exact ⟨mx, fun i => (hmx i).1, fun i => (hmx i).2⟩
  choose m hmf hmμ using hlifts
  have he' := specMap_comp_one D₀
  haveI : IsAffineHom (pullback.fst D₀.f (specMap S (ResidueField S))) := MorphismProperty.pullback_fst _ _ inferInstance
  have hα : ∀ x : Λ, _ := fun x =>
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom S S₀ (algebraMap S S₀) hπ hker hsmall
      f₀ L₀ hL₀ h₀ D₀.f D₀.bundle.smooth D₀.bundle.proper D₀.g D₀.cart
      f₀ L₀ hL₀ h₀ D₀.f D₀.bundle.smooth D₀.bundle.proper D₀.g D₀.cart (D₀.L.one (𝟙 _)) he'
      (act₀ x) (act₀_over x) hI ρS hρScomp V ιV hι hιI 𝒰 (m x) (hmf x) (hmμ x)
      (pullback.snd D₀.f (specMap S (ResidueField S))) (RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L) jκ hakA ((𝒰.baseChange D₀.f (ResidueField S)).U i₀) hU eu₁ heu₁ (pullback.fst D₀.f (specMap S (ResidueField S))) (pullback.snd D₀.f (specMap S (ResidueField S))) hak0
      (fun {n} s => σA n s) (fun {n} s y => (hσA n s).1 y) (fun {n} s a => (hσA n s).2 a)
  choose c₀ hc₀ hc₀Z using hα
  simp only [hjκ] at hc₀

  obtain ⟨θΛ, hθΛ⟩ := CerednikDrinfeld.QM.exists_ringHom_moduleEnd_forall_eq_pushPt (pullback.snd D₀.f (specMap S (ResidueField S))) (RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L) W τW hWinj hWrange hWadd hWsmul ψ hψ hψhom hψone hψmul hψadd
  obtain ⟨ρΛ, hρΛ⟩ := AlgebraicGeometry.OModulePresheaf.exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback (pullback.snd D₀.f (specMap S (ResidueField S))) (RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L) (𝒰.baseChange D₀.f (ResidueField S)) H₁ cls₁ ρ hρid hρcomp hρadd hρpin ψ hψ hψone hψmul hψadd
  obtain ⟨eΛ, heΛ₁, heΛ₂⟩ := IsLocalRing.exists_separabilityElement_residueField_tensor_of_separabilityElement S e he₁ he₂

  obtain ⟨c, hc, hkill⟩ := GoodReductionJacobian.BareDeformation.exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare S S₀ hπ hker hsmall f₀ L₀ hL₀ h₀ hI V ιV hι hιI D₀ 𝒰 i₀ eu₀ heu₀ eu₁ heu₁ (fun s => σA 1 s) (fun s x => (hσA 1 s).1 x) (fun s a => (hσA 1 s).2 a) hU W τW hWinj hWrange hWadd hWsmul Φ hΦnat hΦpin jκ hjκ Λ eΛ heΛ₁ heΛ₂ act₀ act₀_over act₀_hom act₀_one act₀_mul act₀_add ψ hψ hψ₁ hψhom m hmf hmμ c₀ hc₀ hc₀Z θΛ hθΛ H₁ cls₁ hcls₁ hcls₁0 ρΛ hρΛ

  obtain ⟨τ, D, hD, hτ⟩ := GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_bare S S₀ hπ hker hsmall f₀ L₀ hL₀ h₀ hI V ιV hι hιI D₀ 𝒰 i₀ eu₀ heu₀ eu₁ heu₁ (fun s => σA 1 s) (fun s x => (hσA 1 s).1 x) (fun s a => (hσA 1 s).2 a) c hc

  refine ⟨D, fun x => ?_⟩
  obtain ⟨ĉ, hĉ⟩ := exists_pointDerivations_codRestrict ((((𝒰.baseChange D₀.f (ResidueField S)).U i₀).topIso.inv ≫ eu₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField S))).hom).hom)
    (LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap S (ResidueField S)))).d (𝒰.baseChange D₀.f (ResidueField S)) 1)) c (fun a ξ => hc a ξ)
  obtain ⟨ĉ₀, hĉ₀⟩ := exists_pointDerivations_codRestrict ((((𝒰.baseChange D₀.f (ResidueField S)).U i₀).topIso.inv ≫ eu₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField S))).hom).hom)
    (LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap S (ResidueField S)))).d (𝒰.baseChange D₀.f (ResidueField S)) 1)) (c₀ x) (fun a ξ => LinearMap.mem_ker.2 (hc₀Z x a ξ))
  exact (GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare S S₀ hπ hker hsmall f₀ L₀ hL₀ h₀ hI V ιV hι hιI D₀ 𝒰 i₀ eu₀ heu₀ eu₁ heu₁ (fun s => σA 1 s) (fun s x => (hσA 1 s).1 x) (fun s a => (hσA 1 s).2 a) c hc τ D hD hτ hU W τW hWinj hWrange hWadd hWsmul Φ hΦnat hΦpin (act₀ x) (act₀_over x) jκ hjκ (ψ x) (hψ x) (hψ₁ x) (hψhom x) (m x) (hmf x) (hmμ x) (c₀ x) (hc₀ x) (hc₀Z x) (θΛ x : W →ₗ[(ResidueField S)] W) (hθΛ x) H₁ cls₁ hcls₁ hcls₁0 (ρΛ (MulOpposite.op x)) (hρΛ x) ĉ ĉ₀ hĉ₀ hĉ).2 (hkill x ĉ ĉ₀ hĉ₀ hĉ)

end S_GoodReductionJacobian_BareDeformation_exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot (solution)
