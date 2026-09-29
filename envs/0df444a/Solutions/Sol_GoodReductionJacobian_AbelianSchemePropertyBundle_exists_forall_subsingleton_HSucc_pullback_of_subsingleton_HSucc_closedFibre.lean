-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_forall_subsingleton_HSucc_pullback_of_subsingleton_HSucc_closedFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1dba68b9-c8e0-5f3c-862c-e78599547056

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Theorems.Thm_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_forall_subsingleton_HSucc_pullback_of_subsingleton_HSucc_closedFibre
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

noncomputable section

namespace Ws23CBPalpha

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~zero TopologicalSpace Opposite TensorProduct AlgebraicGeometry.Scheme.TwoAffineOpenCover"

def coverOfCompact (X : Scheme.{0}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

theorem isEmpty_idx {X : Scheme.{0}} (𝒰 : X.OrderedAffineCover) (i : ℕ) (hi : Fintype.card 𝒰.ι < i + 1) :
    IsEmpty (𝒰.Idx i) := by
  refine ⟨fun s => ?_⟩
  have h := Fintype.card_le_of_injective s.1 s.2.injective
  rw [Fintype.card_fin] at h
  omega

theorem subsingleton_cochain {R : Type} [CommRing R] {X : Scheme.{0}} {π : X ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (𝒰 : X.OrderedAffineCover) (i : ℕ) (hi : Fintype.card 𝒰.ι ≤ i) :
    Subsingleton (F.cochain 𝒰 i) := by
  haveI : IsEmpty (𝒰.Idx i) := isEmpty_idx 𝒰 i (by omega)
  change Subsingleton (∀ s : 𝒰.Idx i, F.obj (𝒰.inter s))
  infer_instance

theorem ker_le_range_of_subsingleton {A : Type} [CommRing A] {C0 C1 C2 H : Type}
    [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1] [AddCommGroup C2] [Module A C2]
    [AddCommGroup H] [Module A H] [Subsingleton H]
    (d0 : C0 →ₗ[A] C1) (d1 : C1 →ₗ[A] C2) (φ : LinearMap.ker d1 →ₗ[A] H)
    (hφ : LinearMap.ker φ = (LinearMap.range d0).comap (LinearMap.ker d1).subtype) :
    LinearMap.ker d1 ≤ LinearMap.range d0 := by
  intro x hx
  have h1 : (⟨x, hx⟩ : LinearMap.ker d1) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  rw [hφ] at h1
  exact h1

theorem subsingleton_of_ker_le_range {A : Type} [CommRing A] {C0 C1 C2 H : Type}
    [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1] [AddCommGroup C2] [Module A C2]
    [AddCommGroup H] [Module A H]
    (d0 : C0 →ₗ[A] C1) (d1 : C1 →ₗ[A] C2) (φ : LinearMap.ker d1 →ₗ[A] H) (hsurj : Function.Surjective φ)
    (hφ : LinearMap.ker φ = (LinearMap.range d0).comap (LinearMap.ker d1).subtype)
    (h : LinearMap.ker d1 ≤ LinearMap.range d0) : Subsingleton H := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  have hx : x ∈ LinearMap.ker φ := by rw [hφ]; exact h x.2
  have hy : y ∈ LinearMap.ker φ := by rw [hφ]; exact h y.2
  rw [LinearMap.mem_ker] at hx hy
  rw [hx, hy]

section Descent

variable {R : Type} [CommRing R] (κ : Type) [Field κ] [Algebra R κ] (k₀ : Type) [Field k₀] [Algebra R k₀]
  [Algebra κ k₀] [IsScalarTower R κ k₀]
  {C0 C1 C2 : Type} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1] [AddCommGroup C2] [Module R C2]
  (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2)

theorem ladder {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    (g.baseChange k₀) ∘ₗ (AlgebraTensorModule.cancelBaseChange R κ k₀ k₀ M).toLinearMap
      = (AlgebraTensorModule.cancelBaseChange R κ k₀ k₀ N).toLinearMap ∘ₗ (g.baseChange κ).baseChange k₀ := by
  refine TensorProduct.AlgebraTensorModule.ext fun a x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_tmul,
      LinearMap.baseChange_tmul]
  | add x y hx hy =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tmul_add, map_add] at hx hy ⊢
    rw [hx, hy]

include κ k₀ in
theorem ker_le_range_baseChange_of_extension
    (hdd : d1 ∘ₗ d0 = 0)
    (h : LinearMap.ker (d1.baseChange k₀) ≤ LinearMap.range (d0.baseChange k₀)) :
    LinearMap.ker (d1.baseChange κ) ≤ LinearMap.range (d0.baseChange κ) := by

  have hex₀ : Function.Exact (d0.baseChange k₀) (d1.baseChange k₀) := by
    rw [LinearMap.exact_iff]
    refine le_antisymm h ?_
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hdd, LinearMap.baseChange_zero,
      LinearMap.zero_apply]

  have hex₁ : Function.Exact ((d0.baseChange κ).baseChange k₀) ((d1.baseChange κ).baseChange k₀) :=
    (Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R κ k₀ k₀ C0)
      (e₂ := AlgebraTensorModule.cancelBaseChange R κ k₀ k₀ C1)
      (e₃ := AlgebraTensorModule.cancelBaseChange R κ k₀ k₀ C2)
      (ladder κ k₀ d0) (ladder κ k₀ d1)).mp hex₀

  have hex₂ : Function.Exact (d0.baseChange κ) (d1.baseChange κ) :=
    (Module.FaithfullyFlat.lTensor_exact_iff_exact κ k₀ (d0.baseChange κ) (d1.baseChange κ)).mp hex₁
  exact ((LinearMap.exact_iff).mp hex₂).le

end Descent

theorem main
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (s₀ : R →+* k₀) (hs₀ : RingHom.ker s₀ = IsLocalRing.maximalIdeal R)
    (𝒰 : (pullback f (Spec.map (CommRingCat.ofHom s₀))).OrderedAffineCover)
    (hvan : ∀ i : ℕ, Subsingleton
      ((OModulePresheaf.ofModules (pullback.snd f (Spec.map (CommRingCat.ofHom s₀)))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₀)))).obj 𝓛)).HSucc 𝒰 i))
    (K : Type) [Field K] [Algebra R K] :
    ∃ 𝒲 : (pullback f (Scheme.TwoAffineOpenCover.specMap R K)).OrderedAffineCover, ∀ i : ℕ,
      Subsingleton ((OModulePresheaf.ofModules (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R K))
        ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R K))).obj 𝓛)).HSucc 𝒲 i) := by
  classical
  haveI := hA.proper
  haveI := hA.smooth
  haveI : Flat f := inferInstance
  haveI : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  have htriv := h𝓛.exists_trivialization
  let 𝒦 := coverOfCompact A
  let F := OModulePresheaf.ofModules f 𝓛
  haveI : ∀ i, Module.Flat R (F.cochain 𝒦 i) := fun i =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial f 𝓛 htriv 𝒦 i
  have hdd : ∀ i, F.d 𝒦 (i + 1) ∘ₗ F.d 𝒦 i = 0 := fun i => OModulePresheaf.d_comp_d F 𝒦 i
  have hbd : ∀ i, Fintype.card 𝒦.ι ≤ i → Subsingleton (F.cochain 𝒦 i) := fun i hi => subsingleton_cochain F 𝒦 i hi
  have hCF : F.CechFinite 𝒦 := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f 𝓛 htriv 𝒦

  letI algk₀ : Algebra R k₀ := s₀.toAlgebra
  have hk₀ : ∀ i : ℕ, LinearMap.ker ((F.d 𝒦 (i + 1)).baseChange k₀) ≤ LinearMap.range ((F.d 𝒦 i).baseChange k₀) := by
    intro i
    let p₁ := pullback.fst f (specMap R k₀)
    let p₂ := pullback.snd f (specMap R k₀)
    let MK : (pullback f (specMap R k₀)).Modules := (Scheme.Modules.pullback p₁).obj 𝓛
    have htrivK := (h𝓛.pullback p₁).1
    have hq := OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial p₂ MK htrivK
    obtain ⟨eK⟩ := (OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated p₂ MK hq
      (𝒦.baseChange f k₀) 𝒰).2 i
    haveI := hvan i
    haveI : Subsingleton ((OModulePresheaf.ofModules p₂ MK).HSucc (𝒦.baseChange f k₀) i) := eK.toEquiv.subsingleton
    obtain ⟨φ, -, hφ⟩ := (OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial f 𝒦 𝓛 htriv k₀).1.2 i
    exact ker_le_range_of_subsingleton _ _ φ hφ

  let κ := IsLocalRing.ResidueField R
  let ι₀ : κ →+* k₀ := Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) s₀
    (fun a ha => by rwa [← hs₀, RingHom.mem_ker] at ha)
  letI algκk₀ : Algebra κ k₀ := ι₀.toAlgebra
  haveI : IsScalarTower R κ k₀ := IsScalarTower.of_algebraMap_eq (fun r => by
    change ι₀ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) = s₀ r
    exact Ideal.Quotient.lift_mk _ _ _)
  have hκ : ∀ i : ℕ, LinearMap.ker ((F.d 𝒦 (i + 1)).baseChange (IsLocalRing.ResidueField R))
      ≤ LinearMap.range ((F.d 𝒦 i).baseChange (IsLocalRing.ResidueField R)) := fun i =>
    ker_le_range_baseChange_of_extension κ k₀ (F.d 𝒦 i) (F.d 𝒦 (i + 1)) (hdd i) (hk₀ i)

  obtain ⟨-, hall⟩ :=
    Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
      (fun i => F.cochain 𝒦 i) (fun i => F.d 𝒦 i) hdd (Fintype.card 𝒦.ι) hbd hCF.2 hκ

  refine ⟨𝒦.baseChange f K, fun i => ?_⟩
  obtain ⟨φ, hsurj, hφ⟩ := (OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial f 𝒦 𝓛 htriv K).1.2 i
  exact subsingleton_of_ker_le_range _ _ φ hsurj hφ (hall K i)

end Ws23CBPalpha

end

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (s₀ : R →+* k₀) (hs₀ : RingHom.ker s₀ = IsLocalRing.maximalIdeal R)
    (𝒰 : (pullback f (Spec.map (CommRingCat.ofHom s₀))).OrderedAffineCover)
    (hvan : ∀ i : ℕ, Subsingleton
      ((OModulePresheaf.ofModules (pullback.snd f (Spec.map (CommRingCat.ofHom s₀)))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₀)))).obj 𝓛)).HSucc 𝒰 i))
    (K : Type) [Field K] [Algebra R K] :
    ∃ 𝒲 : (pullback f (Scheme.TwoAffineOpenCover.specMap R K)).OrderedAffineCover, ∀ i : ℕ,
      Subsingleton ((OModulePresheaf.ofModules (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R K))
        ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R K))).obj 𝓛)).HSucc 𝒲 i) :=
  Ws23CBPalpha.main f hA 𝓛 h𝓛 k₀ s₀ hs₀ 𝒰 hvan K

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_forall_subsingleton_HSucc_pullback_of_subsingleton_HSucc_closedFibre
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_forall_subsingleton_HSucc_pullback_of_subsingleton_HSucc_closedFibre (solution)
