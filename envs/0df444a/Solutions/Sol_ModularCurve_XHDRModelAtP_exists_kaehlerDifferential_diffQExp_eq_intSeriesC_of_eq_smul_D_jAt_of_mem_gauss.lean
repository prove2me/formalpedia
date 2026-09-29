-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_kaehlerDifferential_diffQExp_eq_intSeriesC_of_eq_smul_D_jAt_of_mem_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0f078a9d-7c4c-550e-a3c3-d95edee8319e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_kaehlerDifferential_diffQExp_eq_intSeriesC_of_eq_smul_D_jAt_of_mem_gauss
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

noncomputable section

namespace E4q

section Series

theorem algebraMap_R_injective (p : ℕ) : Function.Injective (algebraMap (R p) ℚ) := Subtype.val_injective

theorem coeffMap_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun x y h => by
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem coeffMap_qEuler {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (x : LaurentSeries A) :
    coeffMap φ (qEuler A x) = qEuler B (coeffMap φ x) := by
  ext n
  simp [coeffMap_coeff, qEuler_coeff]

theorem map_map_intCast {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (P : PowerSeries ℤ) :
    (P.map (Int.castRingHom A)).map φ = P.map (Int.castRingHom B) := by
  have h := congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom A) φ)) P
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  rw [← h, RingHom.ext_int (φ.comp (Int.castRingHom A)) (Int.castRingHom B)]

end Series

section Local

variable (p : ℕ) [Fact p.Prime]

theorem ratLocalizedAtResidue_eq_zero_of_map_eq_zero {κ : Type} [Field κ] (toκ : R p →+* κ) (r : R p)
    (hr : toκ r = 0) : GaloisRep.ratLocalizedAtResidue p r = 0 := by
  haveI : IsLocalization.AtPrime (R p) (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  haveI : IsLocalRing (R p) := IsLocalization.AtPrime.isLocalRing (R p) (Ideal.span {(p : ℤ)})
  have hnu : ¬ IsUnit r := fun hu => not_isUnit_zero (hr ▸ hu.map toκ)
  have hmax : RingHom.ker (GaloisRep.ratLocalizedAtResidue p) = IsLocalRing.maximalIdeal (R p) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (ZMod.ringHom_surjective _))
  have hmem : r ∈ IsLocalRing.maximalIdeal (R p) := hnu
  rw [← hmax] at hmem
  exact hmem

theorem map_ne_zero_of_map_ratLocalizedAtResidue_ne_zero {κ : Type} [Field κ] (toκ : R p →+* κ)
    (a : PowerSeries (R p)) (ha : a.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0) : a.map toκ ≠ 0 := by
  intro h0
  apply ha
  ext n
  rw [PowerSeries.coeff_map, map_zero]
  apply ratLocalizedAtResidue_eq_zero_of_map_eq_zero p toκ
  have e := congrArg (fun s => PowerSeries.coeff n s) h0
  simpa only [PowerSeries.coeff_map, map_zero] using e

end Local

end E4q

open E4q in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (W₀ : ValuationSubring ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (hW₀ : (∀ f₀ : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)), f₀ ∈ W₀ ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f₀ : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (η : (@KaehlerDifferential ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))))) (g : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (hg : g ∈ W₀)
    (hη : η = g • @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (ModularCurve.XHDRLevel.jAt (ModularCurve.XHDRLevel.ΓM M H) hj))
    (P : PowerSeries ℤ)
    (hΘ : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) η =
      HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ))) :
    ∃ ω : Ω[↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM))⁄(IsLocalRing.ResidueField ↥A)],
      ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM)) ω =
        ModularCurve.intSeriesC (IsLocalRing.ResidueField ↥A) P := by
  classical

  let κ := IsLocalRing.ResidueField ↥A
  let toκ : R p →+* κ := (IsLocalRing.residue ↥A).comp ρ
  haveI : (ΓM M H).FiniteIndex := CuspForm.GammaH_finiteIndex M H
  have hT : ModularGroup.T ∈ ΓM M H := ModularCurve.translation_mem_GammaH M H

  have hjM : jqModC κ ∈ qExpFunctionFieldC κ (ΓM M H) :=
    intFormRatiosC_subset κ (ΓM M H) (ModularCurve.jqModC_mem_intFormRatiosC κ (ΓM M H))
  obtain ⟨V, hRV, red, -, -, -, -, -, hadj, hmemV, hpres⟩ :=
    ModularCurve.exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
      (ΓM M H) hT p (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj) A hA ρ hρ ⟨jqModC κ, hjM⟩ rfl

  obtain ⟨a, a', ha', hga⟩ := (hW₀ g).mp hg
  have hsub : (GaloisRep.ratLocalizedAt p).subtype = algebraMap (R p) ℚ := rfl
  rw [hsub, ← coeffMap_ofPowerSeries, ← coeffMap_ofPowerSeries] at hga

  have hlift : ∀ w : LaurentSeries (R p),
      coeffMap A.subtype (coeffMap ρ w) = coeffEmb (AlgebraicClosure ℚ) (coeffMap (algebraMap (R p) ℚ) w) := by
    intro w
    rw [coeffMap_coeffMap, hρ, coeffEmb, coeffMap_coeffMap]
    congr 1
  have hred' : ∀ w : LaurentSeries (R p), coeffMap (IsLocalRing.residue ↥A) (coeffMap ρ w) = coeffMap toκ w := fun w => by
    rw [coeffMap_coeffMap]
  have ha'κ : HahnSeries.ofPowerSeries ℤ κ (a'.map toκ) ≠ 0 := fun h0 =>
    map_ne_zero_of_map_ratLocalizedAtResidue_ne_zero p toκ a' ha'
      (HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero]))
  have hybar : coeffMap (IsLocalRing.residue ↥A) (coeffMap ρ (HahnSeries.ofPowerSeries ℤ (R p) a')) ≠ 0 := by
    rw [hred', coeffMap_ofPowerSeries]
    exact ha'κ
  have heqA : coeffEmb (AlgebraicClosure ℚ) ((g : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) *
        coeffMap A.subtype (coeffMap ρ (HahnSeries.ofPowerSeries ℤ (R p) a')) =
      coeffMap A.subtype (coeffMap ρ (HahnSeries.ofPowerSeries ℤ (R p) a)) := by
    rw [hlift, hlift, ← map_mul, hga]
  have hgV : g ∈ V := (hmemV g).mpr ⟨_, _, hybar, heqA⟩

  have hredg : red ⟨g, hgV⟩ * HahnSeries.ofPowerSeries ℤ κ (a'.map toκ) = HahnSeries.ofPowerSeries ℤ κ (a.map toκ) := by
    have h := hpres ⟨g, hgV⟩ _ _ hybar heqA
    rwa [hred', hred', coeffMap_ofPowerSeries, coeffMap_ofPowerSeries] at h

  have hmemM : red ⟨g, hgV⟩ ∈ qExpFunctionFieldC κ (ΓM M H) := by
    rw [← hadj]
    exact IntermediateField.subset_adjoin κ _ ⟨_, rfl⟩
  have hle := ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup p M hpM hpM2 H hHp κ
  have hjN : jqModC κ ∈ qExpFunctionFieldC κ (ΓN p M H hpM) :=
    intFormRatiosC_subset κ (ΓN p M H hpM) (ModularCurve.jqModC_mem_intFormRatiosC κ (ΓN p M H hpM))
  let gbar : ↥(qExpFunctionFieldC κ (ΓN p M H hpM)) := ⟨red ⟨g, hgV⟩, hle hmemM⟩
  let jbar : ↥(qExpFunctionFieldC κ (ΓN p M H hpM)) := ⟨jqModC κ, hjN⟩
  refine ⟨gbar • KaehlerDifferential.D κ ↥(qExpFunctionFieldC κ (ΓN p M H hpM)) jbar, ?_⟩
  rw [diffQExp_smul_D]
  show red ⟨g, hgV⟩ * qEuler κ (jqModC κ) = intSeriesC κ P

  have hQ : ((g : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) * qEuler ℚ (jqModC ℚ) =
      HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ)) := by
    rw [← hΘ, hη, diffQExp_smul_D, coe_jAt]

  have hR : HahnSeries.ofPowerSeries ℤ (R p) a * qEuler (R p) (jqModC (R p)) =
      HahnSeries.ofPowerSeries ℤ (R p) (P.map (Int.castRingHom (R p))) * HahnSeries.ofPowerSeries ℤ (R p) a' := by
    apply coeffMap_injective (algebraMap (R p) ℚ) (algebraMap_R_injective p)
    rw [map_mul, map_mul, coeffMap_qEuler, coeffMap_jqModC, coeffMap_ofPowerSeries _ (P.map _), map_map_intCast,
      ← hQ, ← hga, mul_right_comm]

  have hκ : HahnSeries.ofPowerSeries ℤ κ (a.map toκ) * qEuler κ (jqModC κ) =
      intSeriesC κ P * HahnSeries.ofPowerSeries ℤ κ (a'.map toκ) := by
    have e := congrArg (coeffMap toκ) hR
    rw [map_mul, map_mul, coeffMap_qEuler, coeffMap_jqModC, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries,
      coeffMap_ofPowerSeries, map_map_intCast] at e
    exact e

  apply mul_right_cancel₀ ha'κ
  rw [mul_right_comm, hredg, hκ]

end
end S_ModularCurve_XHDRModelAtP_exists_kaehlerDifferential_diffQExp_eq_intSeriesC_of_eq_smul_D_jAt_of_mem_gauss
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_kaehlerDifferential_diffQExp_eq_intSeriesC_of_eq_smul_D_jAt_of_mem_gauss (solution)
