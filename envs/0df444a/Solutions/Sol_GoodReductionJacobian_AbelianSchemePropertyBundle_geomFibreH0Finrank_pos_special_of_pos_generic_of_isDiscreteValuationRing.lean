-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.geomFibreH0Finrank_pos_special_of_pos_generic_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e90b52ca-a170-550a-8441-9a8bb37048d4

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isClosed_setOf_le_finrank_sections_pullback_residueField
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_pos_special_of_pos_generic_of_isDiscreteValuationRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (KK : Type) [Field KK] [Algebra R KK] [IsFractionRing R KK]
    (k : Type) [Field k] (φ : R →+* k) (hφ : Function.Surjective φ)
    {A AK Ak : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (hA : AbelianSchemePropertyBundle R f)
    (fK : AK ⟶ Spec (CommRingCat.of KK)) (gK : AK ⟶ A) (hgK : IsPullback gK fK f (Spec.map (CommRingCat.ofHom (algebraMap R KK))))
    (fk : Ak ⟶ Spec (CommRingCat.of k)) (gk : Ak ⟶ A) (hgk : IsPullback gk fk f (Spec.map (CommRingCat.ofHom φ)))
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (𝓛K : AK.Modules) (hiso : Nonempty ((Scheme.Modules.pullback gK).obj 𝓛 ≅ 𝓛K))
    (hpos : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : KK →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank fK 𝓛K k' sk) :
    ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'),
      0 < Scheme.Modules.geomFibreH0Finrank fk ((Scheme.Modules.pullback gk).obj 𝓛) k' sk := by
  intro k' _ _ sk
  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth

  rw [Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback φ f fk gk hgk 𝓛 _ (Iso.refl _) k' sk]
  have hpos' : ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (sK : KK →+* K'),
      0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 K' (sK.comp (algebraMap R KK)) := by
    intro K' _ _ sK
    rw [← Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback (algebraMap R KK) f fK gK hgK 𝓛 𝓛K hiso.some K' sK]
    exact hpos K' sK

  let Z : Set (PrimeSpectrum R) := {𝔭 : PrimeSpectrum R |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj 𝓛) ⊤
      1 ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj 𝓛, ⊤)}
  have hZ : IsClosed Z :=
    Scheme.Modules.isClosed_setOf_le_finrank_sections_pullback_residueField f 𝓛 h𝓛.exists_trivialization 1
  have hZiff : ∀ 𝔭 : PrimeSpectrum R, 𝔭 ∈ Z ↔
      1 ≤ Scheme.Modules.geomFibreH0Finrank f 𝓛 𝔭.asIdeal.ResidueField (algebraMap R 𝔭.asIdeal.ResidueField) :=
    fun 𝔭 => Iff.rfl

  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ∈ Z := by
    rw [hZiff]
    let κ := η.asIdeal.ResidueField
    let Kb := AlgebraicClosure κ
    let g : R →+* Kb := (algebraMap κ Kb).comp (algebraMap R κ)
    have hg_inj : Function.Injective g := by
      apply (algebraMap κ Kb).injective.comp
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
    have hg : ∀ y : nonZeroDivisors R, IsUnit (g y) := by
      intro y
      apply IsUnit.mk0 _
      intro h0
      apply nonZeroDivisors.ne_zero y.2
      apply hg_inj
      rw [h0, map_zero]
    let sK : KK →+* Kb := IsLocalization.lift (M := nonZeroDivisors R) (S := KK) hg
    have hsK : sK.comp (algebraMap R KK) = g := IsLocalization.lift_comp hg
    have h1 := hpos' Kb sK
    rw [hsK, Scheme.Modules.geomFibreH0Finrank_comp_eq f 𝓛 h𝓛 κ Kb (algebraMap R κ) (algebraMap κ Kb)] at h1
    exact h1

  haveI hmprime : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  let m : PrimeSpectrum R := ⟨RingHom.ker φ, hmprime⟩
  have hm : m ∈ Z := by
    have hsp : η ⤳ m := (PrimeSpectrum.le_iff_specializes η m).mp (fun x hx => by
      have : x = 0 := hx
      rw [this]; exact Ideal.zero_mem _)
    exact hsp.mem_closed hZ hη
  rw [hZiff] at hm

  let κm := m.asIdeal.ResidueField
  have hf₁ : RingHom.ker φ ≤ RingHom.ker (sk.comp φ) := fun x hx => by
    rw [RingHom.mem_ker] at hx ⊢
    rw [RingHom.comp_apply, hx, map_zero]
  have hf₂ : (RingHom.ker φ).primeCompl ≤ (IsUnit.submonoid k').comap (sk.comp φ) := fun x hx => by
    show IsUnit ((sk.comp φ) x)
    apply IsUnit.mk0 _
    intro h0
    apply hx
    rw [RingHom.comp_apply] at h0
    exact (map_eq_zero_iff sk sk.injective).mp h0
  let j : κm →+* k' := Ideal.ResidueField.lift (RingHom.ker φ) (sk.comp φ) hf₁ hf₂
  have hj : j.comp (algebraMap R κm) = sk.comp φ := by
    ext r
    exact Ideal.ResidueField.lift_algebraMap (RingHom.ker φ) (sk.comp φ) hf₁ hf₂ r
  rw [← hj, Scheme.Modules.geomFibreH0Finrank_comp_eq f 𝓛 h𝓛 κm k' (algebraMap R κm) j]
  exact hm

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_pos_special_of_pos_generic_of_isDiscreteValuationRing
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_pos_special_of_pos_generic_of_isDiscreteValuationRing (solution)
