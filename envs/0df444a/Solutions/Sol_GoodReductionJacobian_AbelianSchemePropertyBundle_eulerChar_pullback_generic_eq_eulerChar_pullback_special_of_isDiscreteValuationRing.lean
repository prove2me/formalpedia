-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_pullback_generic_eq_eulerChar_pullback_special_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ca768083-c2e2-5fb8-a316-f572e961d5a7

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_pullback_generic_eq_eulerChar_pullback_special_of_isDiscreteValuationRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace ChiConstDVR

theorem nonempty_orderedAffineCover (X : Scheme.{u}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by
  classical
  let 𝒱 := X.affineCover.finiteSubcover
  letI : LinearOrder 𝒱.I₀ := LinearOrder.lift' (Fintype.equivFin 𝒱.I₀) (Fintype.equivFin 𝒱.I₀).injective
  exact ⟨Scheme.OrderedAffineCover.mk (ι := 𝒱.I₀) (U := fun j => (𝒱.f j).opensRange)
    (isAffineOpen := fun j => isAffineOpen_opensRange (𝒱.f j)) (iSup_eq_top := 𝒱.iSup_opensRange)⟩

theorem isEmpty_idx {V : Scheme.{u}} (K : V.OrderedAffineCover) {i : ℕ} (hi : Fintype.card K.ι < i + 1) :
    IsEmpty (K.Idx i) := by
  refine ⟨fun s => ?_⟩
  have := Fintype.card_le_of_injective s.1 s.2.injective
  simp only [Fintype.card_fin] at this
  omega

theorem cechFinrank_eq_zero_of_card_le {R : Type u} [CommRing R] [Nontrivial R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {n : ℕ} (hn : Fintype.card K.ι ≤ n) :
    F.cechFinrank K n = 0 := by
  haveI : IsEmpty (K.Idx n) := isEmpty_idx K (by omega)
  haveI : Subsingleton (F.cochain K n) := inferInstance
  cases n with
  | zero =>
    rw [OModulePresheaf.cechFinrank_zero]
    haveI : Subsingleton (F.H0 K) := inferInstance
    exact Module.finrank_zero_of_subsingleton
  | succ i =>
    rw [OModulePresheaf.cechFinrank_succ]
    haveI : Subsingleton (LinearMap.ker (F.d K (i + 1))) := inferInstance
    haveI : Subsingleton (F.HSucc K i) := Quot.Subsingleton
    exact Module.finrank_zero_of_subsingleton

theorem eulerChar_eq_of_forall_cechFinrank_eq {R R' : Type u} [CommRing R] [CommRing R'] [Nontrivial R] [Nontrivial R']
    {V V' : Scheme.{u}}
    {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R')} (F : OModulePresheaf π) (F' : OModulePresheaf π')
    (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover) (h : ∀ n, F.cechFinrank K n = F'.cechFinrank K' n) :
    F.eulerChar K = F'.eulerChar K' := by
  rw [OModulePresheaf.eulerChar_def, OModulePresheaf.eulerChar_def]
  have h1 : ∀ n ≥ Fintype.card K.ι, (-1 : ℤ) ^ n * (F.cechFinrank K n : ℤ) = 0 := fun n hn => by
    rw [cechFinrank_eq_zero_of_card_le F K hn]; simp
  have h2 : ∀ n ≥ Fintype.card K'.ι, (-1 : ℤ) ^ n * (F'.cechFinrank K' n : ℤ) = 0 := fun n hn => by
    rw [cechFinrank_eq_zero_of_card_le F' K' hn]; simp
  rw [← Finset.eventually_constant_sum h1 (le_max_left (Fintype.card K.ι) (Fintype.card K'.ι)),
    ← Finset.eventually_constant_sum h2 (le_max_right (Fintype.card K.ι) (Fintype.card K'.ι))]
  exact Finset.sum_congr rfl fun n _ => by rw [h n]

theorem cechFinrank_congr {R : Type u} [CommRing R] {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (hπ : π = π')
    {N N' : V.Modules} (e : N ≅ N') (K : V.OrderedAffineCover) (n : ℕ) :
    (OModulePresheaf.ofModules π N).cechFinrank K n = (OModulePresheaf.ofModules π' N').cechFinrank K n := by
  subst hπ
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso π e K
  cases n with
  | zero => rw [OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_zero]; exact e0.finrank_eq
  | succ i => rw [OModulePresheaf.cechFinrank_succ, OModulePresheaf.cechFinrank_succ]; exact (hS i).some.finrank_eq

theorem eulerChar_eq_of_isPullback {R : Type u} [CommRing R] (B : Type u) [CommRing B] [Nontrivial B] [Algebra R B]
    {A AB : Scheme.{u}} (f : A ⟶ Spec (.of R)) [IsSeparated f]
    (fB : AB ⟶ Spec (.of B)) (g : AB ⟶ A)
    (hg : IsPullback g fB f (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (𝒦 : AB.OrderedAffineCover) (𝒰 : A.OrderedAffineCover) :
    (OModulePresheaf.ofModules fB ((Scheme.Modules.pullback g).obj 𝓛)).eulerChar 𝒦 =
      (OModulePresheaf.ofModules (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B))).obj 𝓛)).eulerChar
        (𝒰.baseChange f B) := by
  let ι := Scheme.TwoAffineOpenCover.specMap R B
  have hg' : IsPullback g fB f ι := hg
  let e := hg'.isoPullback
  have h1 : e.hom ≫ pullback.fst f ι = g := hg'.isoPullback_hom_fst
  have h2 : e.hom ≫ pullback.snd f ι = fB := hg'.isoPullback_hom_snd
  have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (pullback.fst f ι)).obj 𝓛) := h𝓛.pullback _
  apply eulerChar_eq_of_forall_cechFinrank_eq
  intro n
  rw [← OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso (pullback.snd f ι) e.hom
    ((Scheme.Modules.pullback (pullback.fst f ι)).obj 𝓛) hN 𝒦 (𝒰.baseChange f B) n]

  refine cechFinrank_congr h2.symm ?_ 𝒦 n
  exact ((Scheme.Modules.pullbackCongr h1).app 𝓛).symm ≪≫ ((Scheme.Modules.pullbackComp e.hom (pullback.fst f ι)).app 𝓛).symm

end ChiConstDVR

open ChiConstDVR in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (KK : Type) [Field KK] [Algebra R KK] [IsFractionRing R KK]
    (k : Type) [Field k] (φ : R →+* k) (hφ : Function.Surjective φ)
    {A AK Ak : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (hA : AbelianSchemePropertyBundle R f)
    (fK : AK ⟶ Spec (CommRingCat.of KK)) (gK : AK ⟶ A) (hgK : IsPullback gK fK f (Spec.map (CommRingCat.ofHom (algebraMap R KK))))
    (fk : Ak ⟶ Spec (CommRingCat.of k)) (gk : Ak ⟶ A) (hgk : IsPullback gk fk f (Spec.map (CommRingCat.ofHom φ)))
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (𝒦K : AK.OrderedAffineCover) (𝒦k : Ak.OrderedAffineCover) :
    (OModulePresheaf.ofModules fK ((Scheme.Modules.pullback gK).obj 𝓛)).eulerChar 𝒦K =
      (OModulePresheaf.ofModules fk ((Scheme.Modules.pullback gk).obj 𝓛)).eulerChar 𝒦k := by
  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  haveI : Flat f := inferInstance
  haveI : CompactSpace ↥A := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨𝒰⟩ := nonempty_orderedAffineCover A
  obtain ⟨χ₀, hχ⟩ :=
    OModulePresheaf.exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing f 𝓛 h𝓛.exists_trivialization 𝒰

  have hK := eulerChar_eq_of_isPullback KK f fK gK hgK 𝓛 h𝓛 𝒦K 𝒰

  letI : Algebra R k := φ.toAlgebra
  have hgk' : IsPullback gk fk f (Spec.map (CommRingCat.ofHom (algebraMap R k))) := hgk
  have hk := eulerChar_eq_of_isPullback k f fk gk hgk' 𝓛 h𝓛 𝒦k 𝒰
  rw [hK, hk, hχ KK, hχ k]

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_pullback_generic_eq_eulerChar_pullback_special_of_isDiscreteValuationRing
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_pullback_generic_eq_eulerChar_pullback_special_of_isDiscreteValuationRing (solution)
