-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_preimage_iotaFin_pullback_toBase_specMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/76ea9ab6-6cfb-5539-840c-788394f2447c

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_preimage_iotaFin_pullback_toBase_specMap

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

private theorem charZero_of_ratLocalizedAt (q : ℕ) [Fact q.Prime] {O : Type} [CommRing O] [IsDomain O]
    (ρ : ↥(GaloisRep.ratLocalizedAt q) →+* O) (hq : ((q : ℕ) : O) ≠ 0) : CharZero O := by
  refine ⟨fun m n hmn => ?_⟩

  suffices key : ∀ k : ℕ, (k : O) = 0 → k = 0 by
    rcases Nat.le_total m n with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have : (d : O) = 0 := by
        have := hmn; push_cast at this; linear_combination -this
      simp [key d this]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have : (d : O) = 0 := by
        have := hmn; push_cast at this; linear_combination this
      simp [key d this]
  intro k hk
  by_contra hk0

  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 q (Fact.out : q.Prime).ne_one

  have hmem : ((m : ℚ)⁻¹) ∈ GaloisRep.ratLocalizedAt q := by
    show ((m : ℚ)⁻¹).den.Coprime q
    have hm0 : m ≠ 0 := by rintro rfl; simp at hk0
    rw [Rat.inv_natCast_den_of_pos (Nat.pos_of_ne_zero hm0)]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hm).symm
  have hunit : IsUnit ((m : ℕ) : O) := by
    refine isUnit_iff_exists_inv.mpr ⟨ρ ⟨(m : ℚ)⁻¹, hmem⟩, ?_⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      have : m ≠ 0 := by rintro rfl; simp at hk0
      exact_mod_cast this
    have : ((m : ↥(GaloisRep.ratLocalizedAt q)) * ⟨(m : ℚ)⁻¹, hmem⟩ : ↥(GaloisRep.ratLocalizedAt q)) = 1 := by
      apply Subtype.ext
      push_cast
      exact mul_inv_cancel₀ hm0
    have h2 := congrArg ρ this
    rw [map_mul, map_one, map_natCast] at h2
    exact h2
  have : ((q : O) ^ a) * (m : O) = 0 := by exact_mod_cast hk
  rcases mul_eq_zero.mp this with h | h
  · exact hq (pow_eq_zero_iff'.mp h).1
  · exact hunit.ne_zero h

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O) :
    Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))) := by
  classical

  have hq0 : ((q : ℕ) : O) ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field O
    rw [hϖO, h, Ideal.span_singleton_eq_bot.mpr rfl]
  haveI : CharZero O := charZero_of_ratLocalizedAt q ρO hq0
  have hρinj : Function.Injective ρO := by
    intro a b hab
    rw [← sub_eq_zero] at hab ⊢
    rw [← map_sub] at hab
    set r := a - b with hr

    have hmemd : (((r : ℚ).den : ℕ) : ℚ) ∈ GaloisRep.ratLocalizedAt q := by
      show ((((r : ℚ).den : ℕ) : ℚ)).den.Coprime q
      simp
    have hmemn : (((r : ℚ).num : ℤ) : ℚ) ∈ GaloisRep.ratLocalizedAt q := by
      show ((((r : ℚ).num : ℤ) : ℚ)).den.Coprime q
      simp
    have h1 : r * ⟨_, hmemd⟩ = (⟨_, hmemn⟩ : ↥(GaloisRep.ratLocalizedAt q)) := by
      apply Subtype.ext
      show (r : ℚ) * ((r : ℚ).den : ℚ) = ((r : ℚ).num : ℚ)
      exact Rat.mul_den_eq_num (r : ℚ)
    have h2 := congrArg ρO h1
    rw [map_mul, hab, zero_mul] at h2
    have hn : ρO ⟨_, hmemn⟩ = (((r : ℚ).num : ℤ) : O) := by
      have : (⟨_, hmemn⟩ : ↥(GaloisRep.ratLocalizedAt q)) = (((r : ℚ).num : ℤ) : ↥(GaloisRep.ratLocalizedAt q)) :=
        Subtype.ext (by push_cast; rfl)
      rw [this, map_intCast]
    rw [hn] at h2
    have hnum : (r : ℚ).num = 0 := by exact_mod_cast h2.symm
    apply Subtype.ext
    show (r : ℚ) = 0
    exact Rat.zero_of_num_zero hnum

  haveI := 𝔓.Meta_chart_nonempty
  obtain ⟨m⟩ := (inferInstance : Nonempty (Scheme.Opens.toScheme ((𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q)
    (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))))
  set x₀ : ↥(DRLevel.X N₀ q) := (𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _).base m.1 with hx₀
  have hx₀mem : x₀ ∈ (IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤ := m.2

  let y : ↥(Spec (CommRingCat.of O)) := ⟨⊥, Ideal.isPrime_bot⟩
  have hbase : (DRLevel.toBase N₀ q).base x₀ = (Spec.map (CommRingCat.ofHom ρO)).base y := by
    have h1 : (DRLevel.toBase N₀ q).base x₀ =
        (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))).base
          ((𝔓.eeta ≫ pullback.snd _ _).base m.1) := by
      rw [hx₀]
      show ((𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _) ≫ DRLevel.toBase N₀ q).base m.1 = _
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      rfl
    rw [h1]
    apply PrimeSpectrum.ext
    rw [Spec.map_apply, Spec.map_apply, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]

    have hpt : ((𝔓.eeta ≫ pullback.snd _ _).base m.1).asIdeal = ⊥ := by
      rw [← IsLocalRing.maximalIdeal_eq_bot (R := AlgebraicClosure ℚ)]
      exact congrArg PrimeSpectrum.asIdeal (Subsingleton.elim _ (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))
    rw [hpt]
    show Ideal.comap (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)) ⊥ = Ideal.comap ρO ⊥
    rw [← RingHom.ker_eq_comap_bot, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hρinj,
      (RingHom.injective_iff_ker_eq_bot _).mp]
    rw [IsScalarTower.algebraMap_eq (DRLevel.R q) ℚ (AlgebraicClosure ℚ)]
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp Subtype.val_injective
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := DRLevel.toBase N₀ q) (g := Spec.map (CommRingCat.ofHom ρO)) x₀ y hbase
  exact ⟨⟨z, show (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base z ∈ _ by rw [hz]; exact hx₀mem⟩⟩

end S_ModularCurve_DRModelPackageLevel_nonempty_preimage_iotaFin_pullback_toBase_specMap
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_preimage_iotaFin_pullback_toBase_specMap (solution)
