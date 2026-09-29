-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_iso_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/9f8113e1-c5fd-53f4-b6a7-aafe374f4cac

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_of_isProper
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_iso_of_finite
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AutFinFqT

section Npow
variable {B X : Scheme.{0}} {f : X ⟶ B}

theorem npow_add (β : SchemeHomOver f f) (a b : ℕ) :
    schemeHomOverNpow β (a + b) = NeronModelInfra.schemeHomOverComp (schemeHomOverNpow β a) (schemeHomOverNpow β b) := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.add_succ, schemeHomOverNpow_succ, ih, schemeHomOverNpow_succ, schemeHomOverComp_assoc]

theorem npow_isIso (β : SchemeHomOver f f) [IsIso β.1] (i : ℕ) : IsIso (schemeHomOverNpow β i).1 := by
  induction i with
  | zero => rw [schemeHomOverNpow_zero, schemeHomOverId_coe]; infer_instance
  | succ i ih => rw [schemeHomOverNpow_succ, NeronModelInfra.schemeHomOverComp_coe]; exact IsIso.comp_isIso

end Npow

theorem main
    {k₀ : Type} [Field k₀] [Finite k₀]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k₀)} (hA : AbelianSchemePropertyBundle k₀ f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (hci : Scheme.Modules.ClosedImmersionBySections M f)
    (σ : SchemeHomOver f f) (hσiso : IsIso σ.1)
    (hpol : ∀ s : ↥(Spec (CommRingCat.of k₀)), ∃ U : (Spec (CommRingCat.of k₀)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj M) ≅
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    ∃ m : ℕ, m ≠ 0 ∧ NeronModelInfra.schemeHomOverNpow σ m = NeronModelInfra.schemeHomOverId f := by
  classical
  haveI := hσiso
  obtain ⟨N, 𝔓, h𝔓⟩ := hci

  obtain ⟨φ⟩ := (AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_field f
    ((Scheme.Modules.pullback σ.1).obj M) M).mp hpol

  have hiso : ∀ i : ℕ, Nonempty ((Scheme.Modules.pullback (schemeHomOverNpow σ i).1).obj M ≅ M) := by
    intro i
    induction i with
    | zero =>
      rw [schemeHomOverNpow_zero, schemeHomOverId_coe]
      exact ⟨(Scheme.Modules.pullbackId A).app M⟩
    | succ i ih =>
      obtain ⟨ψ⟩ := ih
      rw [schemeHomOverNpow_succ, NeronModelInfra.schemeHomOverComp_coe]
      exact ⟨((Scheme.Modules.pullbackComp (schemeHomOverNpow σ i).1 σ.1).app M).symm ≪≫
        (Scheme.Modules.pullback (schemeHomOverNpow σ i).1).mapIso φ ≪≫ ψ⟩

  have hsq1 : Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀)) = 𝟙 (Spec (CommRingCat.of k₀)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have step : ∀ i : ℕ, ∃ 𝔔 : M.ProjPresentation f N,
      𝔔.toProj ≫ ProjSpace.map k₀ k₀ N = (schemeHomOverNpow σ i).1 ≫ 𝔓.toProj := by
    intro i
    haveI : IsIso (schemeHomOverNpow σ i).1 := npow_isIso σ i
    obtain ⟨φi⟩ := hiso i
    have sq : IsPullback (schemeHomOverNpow σ i).1 f f (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀))) := by
      rw [hsq1]
      exact IsPullback.of_horiz_isIso ⟨by rw [(schemeHomOverNpow σ i).2, Category.comp_id]⟩
    obtain ⟨𝔓', -, htoProj, -⟩ := Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback sq 𝔓
    obtain ⟨𝔔, hQto, -⟩ := Scheme.Modules.ProjPresentation.exists_of_iso 𝔓' φi
    exact ⟨𝔔, by rw [hQto, htoProj]⟩
  choose Q hQ using step

  haveI : IsProper f := hA.proper
  have hfin : Finite (Γ(M, ⊤)) := by
    letI : Algebra k₀ Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k₀)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module k₀ Γ(M, ⊤) := Module.compHom _ (algebraMap k₀ Γ(A, ⊤))
    haveI := Scheme.Modules.IsInvertible.finite_sections_of_isProper k₀ f M hM
    exact Module.finite_of_finite k₀

  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (Q i).σ)
  have htp : (Q i).toProj = (Q j).toProj :=
    Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq (Q i) (Q j) (fun l => congrFun hij l)
  have hcomp : (schemeHomOverNpow σ i).1 ≫ 𝔓.toProj = (schemeHomOverNpow σ j).1 ≫ 𝔓.toProj := by
    rw [← hQ i, ← hQ j, htp]
  haveI : Mono 𝔓.toProj := inferInstance
  have heq : (schemeHomOverNpow σ i).1 = (schemeHomOverNpow σ j).1 := (cancel_mono _).mp hcomp

  have finish : ∀ a b : ℕ, a < b → (schemeHomOverNpow σ a).1 = (schemeHomOverNpow σ b).1 →
      ∃ m : ℕ, m ≠ 0 ∧ schemeHomOverNpow σ m = schemeHomOverId f := by
    intro a b hab hval
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine ⟨m + 1, Nat.succ_ne_zero m, ?_⟩
    haveI : IsIso (schemeHomOverNpow σ a).1 := npow_isIso σ a
    apply Subtype.ext
    rw [schemeHomOverId_coe]
    have h2 := hval
    rw [show a + m + 1 = a + (m + 1) by omega, npow_add, NeronModelInfra.schemeHomOverComp_coe] at h2
    rw [← cancel_epi (schemeHomOverNpow σ a).1, ← h2, Category.comp_id]
  rcases lt_or_gt_of_ne hne with h | h
  · exact finish i j h heq
  · exact finish j i h heq.symm

end AutFinFqT

theorem solution
    {k₀ : Type} [Field k₀] [Finite k₀]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k₀)} (hA : AbelianSchemePropertyBundle k₀ f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (hci : Scheme.Modules.ClosedImmersionBySections M f)
    (σ : SchemeHomOver f f) (hσiso : IsIso σ.1)
    (hpol : ∀ s : ↥(Spec (CommRingCat.of k₀)), ∃ U : (Spec (CommRingCat.of k₀)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj M) ≅
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    ∃ m : ℕ, m ≠ 0 ∧ NeronModelInfra.schemeHomOverNpow σ m = NeronModelInfra.schemeHomOverId f :=
  AutFinFqT.main hA M hM hci σ hσiso hpol

#print axioms solution

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_iso_of_finite
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_iso_of_finite (solution)
