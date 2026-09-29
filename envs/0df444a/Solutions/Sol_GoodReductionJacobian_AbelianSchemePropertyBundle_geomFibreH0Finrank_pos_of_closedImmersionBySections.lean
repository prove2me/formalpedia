-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.geomFibreH0Finrank_pos_of_closedImmersionBySections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/40024db2-39b8-5323-8622-d886fb1765ea

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_pos_of_closedImmersionBySections
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_pos_of_closedImmersionBySections.AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Spec.map Scheme Scheme.basicOpen_zero Proj Proj.basicOpen Scheme.Modules Scheme.basicOpen_one Proj.iSup_basicOpen_eq_top Scheme.ΓSpecIso Scheme.Modules.geomFibreH0Finrank PolarisedAbelianScheme Scheme.Modules.IsInvertible Scheme.Modules.ProjPresentation Scheme.Modules.ClosedImmersionBySections ProjSpace.irrelevant_le_span_X Scheme.Modules.IsInvertible.finite_sections_of_isProper Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Γ empty basicOpen_zero basicOpen Modules Opens basicOpen_one ΓSpecIso Modules.geomFibreH0Finrank Modules.IsInvertible Modules.ProjPresentation Modules.ClosedImmersionBySections Modules.IsInvertible.finite_sections_of_isProper Modules.ProjPresentation.exists_baseChange_of_isPullback" end AlgebraicGeometry.Scheme
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme" in

theorem AlgebraicGeometry.Scheme.one_ne_zero_of_mem {X : Scheme.{0}} {U : X.Opens} {x : X} (hx : x ∈ U) :
    (1 : Γ(X, U)) ≠ 0 := by
  intro h
  have hU : U = ⊥ := by rw [← Scheme.basicOpen_one (X := X) (U := U), h, Scheme.basicOpen_zero]
  rw [hU] at hx
  exact hx

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Spec.map Scheme Scheme.basicOpen_zero Proj Proj.basicOpen Scheme.Modules Scheme.basicOpen_one Proj.iSup_basicOpen_eq_top Scheme.ΓSpecIso Scheme.Modules.geomFibreH0Finrank PolarisedAbelianScheme Scheme.Modules.IsInvertible Scheme.Modules.ProjPresentation Scheme.Modules.ClosedImmersionBySections ProjSpace.irrelevant_le_span_X Scheme.Modules.IsInvertible.finite_sections_of_isProper Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Γ empty basicOpen_zero basicOpen Modules Opens basicOpen_one ΓSpecIso Modules.geomFibreH0Finrank Modules.IsInvertible Modules.ProjPresentation Modules.ClosedImmersionBySections Modules.IsInvertible.finite_sections_of_isProper Modules.ProjPresentation.exists_baseChange_of_isPullback" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback geomFibreH0Finrank IsInvertible ProjPresentation ClosedImmersionBySections IsInvertible.finite_sections_of_isProper ProjPresentation.exists_baseChange_of_isPullback" namespace ProjPresentation p2m_export "AlgebraicGeometry.Scheme.Modules.ProjPresentation" "toProj frame σ exists_baseChange_of_isPullback" end AlgebraicGeometry.Scheme.Modules.ProjPresentation
namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.ProjPresentation" in

private theorem _root_.AlgebraicGeometry.Scheme.Modules.ProjPresentation.σ_ne_zero_of_mem
    {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (i : Fin (N + 1)) {x : X}
    (hx : x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) :
    𝔓.σ i ≠ 0 := by
  intro h0
  have hbij := 𝔓.frame i _ le_rfl
  apply AlgebraicGeometry.Scheme.one_ne_zero_of_mem hx
  apply hbij.1
  simp only [h0, map_zero, smul_zero]

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
p2m_export "" "AlgebraicGeometry.Scheme.Modules.ProjPresentation.σ_ne_zero_of_mem"
namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.ProjPresentation" in

private theorem _root_.AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_mem_chart
    {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (x : X) :
    ∃ i : Fin (N + 1), x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) := by
  have hx : 𝔓.toProj.base x ∈ (⨆ i : Fin (N + 1),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) := by
    rw [Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R N)]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨i, hi⟩

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
p2m_export "" "AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_mem_chart"

theorem solution
    {R : Type} [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k) :
    0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk := by
  haveI := hA.proper
  obtain ⟨L⟩ := hA.hasGroupLaw
  obtain ⟨N, 𝔓, -⟩ := hva
  letI : Algebra R k := sk.toAlgebra

  letI algP : Algebra k Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI modP : Module k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓛, ⊤) :=
    Module.compHom _ (algebraMap k Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤))
  show 0 < Module.finrank k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓛, ⊤)

  haveI hfin : Module.Finite k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓛, ⊤) :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.finite_sections_of_isProper k
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))) _ (h𝓛.pullback _)

  obtain ⟨𝔓', -, -, -⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback (R := R) (A := k)
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom sk))) 𝔓
  let e : Spec (.of k) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom sk)) :=
    Limits.pullback.lift (L.one (Spec.map (CommRingCat.ofHom sk))).1 (𝟙 _)
      (by rw [(L.one (Spec.map (CommRingCat.ofHom sk))).2, Category.id_comp])
  let x : ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom sk))) := e.base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  obtain ⟨i, hi⟩ := 𝔓'.exists_mem_chart x
  have hσ : 𝔓'.σ i ≠ 0 := 𝔓'.σ_ne_zero_of_mem i hi
  rw [Module.finrank_pos_iff_exists_ne_zero]
  exact ⟨𝔓'.σ i, hσ⟩

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_pos_of_closedImmersionBySections
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_pos_of_closedImmersionBySections (solution)
