-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/2122d514-bd22-56d0-8dfe-c2f5cf9f6cdc

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace ReadKillAux

theorem div_mem_of_residue_eq_zero {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L) (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥A) q] (r : ℚ) (hr : algebraMap ℚ L r ∈ A)
    (h0 : IsLocalRing.residue ↥A ⟨algebraMap ℚ L r, hr⟩ = 0) :
    algebraMap ℚ L (r / q) ∈ A := by
  have hqp : q.Prime := Fact.out
  have key : (⟨algebraMap ℚ L r, hr⟩ : ↥A) * ((r.den : ℕ) : ↥A) = ((r.num : ℤ) : ↥A) := by
    apply Subtype.ext
    show algebraMap ℚ L r * (((r.den : ℕ) : ↥A) : L) = (((r.num : ℤ) : ↥A) : L)
    rw [SubringClass.coe_natCast, SubringClass.coe_intCast, ← map_natCast (algebraMap ℚ L), ← map_intCast (algebraMap ℚ L),
      ← map_mul, Rat.mul_den_eq_num]
  have key2 : IsLocalRing.residue ↥A ⟨algebraMap ℚ L r, hr⟩ * ((r.den : ℕ) : IsLocalRing.ResidueField ↥A) =
      ((r.num : ℤ) : IsLocalRing.ResidueField ↥A) := by
    have h := congrArg (IsLocalRing.residue ↥A) key
    rwa [map_mul, map_natCast, map_intCast] at h
  have hnum0 : ((r.num : ℤ) : IsLocalRing.ResidueField ↥A) = 0 := by rw [← key2, h0, zero_mul]
  have hqnum : (q : ℤ) ∣ r.num := (CharP.intCast_eq_zero_iff (IsLocalRing.ResidueField ↥A) q _).mp hnum0

  have hqden : ¬ q ∣ r.den := by
    intro hd
    have h1 : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd (Int.natCast_dvd.mp hqnum) hd
    rw [r.reduced] at h1
    exact hqp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hden0 : ((r.den : ℕ) : IsLocalRing.ResidueField ↥A) ≠ 0 := fun h =>
    hqden ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥A) q _).mp h)
  have hdenU : IsUnit ((r.den : ℕ) : ↥A) := by
    by_contra hnu
    apply hden0
    rw [← map_natCast (IsLocalRing.residue ↥A), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
  obtain ⟨u, hu⟩ := hdenU

  obtain ⟨c, hc⟩ := hqnum
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hd0 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hr' : r / q = (c : ℚ) / (r.den : ℚ) := by
    rw [div_eq_div_iff hq0 hd0]
    have hmd := Rat.mul_den_eq_num r
    rw [hmd, hc]; push_cast; ring
  rw [hr', map_div₀, map_intCast, map_natCast, div_eq_mul_inv]
  refine mul_mem (intCast_mem A c) ?_

  have hinv : ((r.den : ℕ) : L)⁻¹ = (((u⁻¹ : (↥A)ˣ) : ↥A) : L) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    have hcast : ((r.den : ℕ) : L) = (((r.den : ℕ) : ↥A) : L) := by rw [SubringClass.coe_natCast]
    rw [hcast, ← hu, ← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
  rw [hinv]
  exact ((u⁻¹ : (↥A)ˣ) : ↥A).2

end ReadKillAux

open ReadKillAux in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
      ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')))
    (hres : R₀.residue ⟨_, hgi⟩ = 0) :
    ∃ (g' : LaurentSeries ℚ) (hg' : g' ∈ modularFunctionFieldFull M'),
      g = (q : ℚ) • g' ∧
      (⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers ∧
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) := by
  classical
  haveI hchar : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  have hqp : q.Prime := Fact.out

  have hint : ∀ k : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff k) ∈ A :=
    ModularCurve.algebraMap_coeff_mem_of_mem_integers_of_cuspRegular q M' A hA R₀ hR₀ g hg hgi hcusp
  let y : LaurentSeries ↥A :=
    { coeff := fun k => ⟨(coeffEmb (AlgebraicClosure ℚ) g).coeff k, hint k⟩
      isPWO_support' := (coeffEmb (AlgebraicClosure ℚ) g).isPWO_support'.mono (by
        intro k hk
        simp only [Function.mem_support, ne_eq] at hk ⊢
        exact fun h0 => hk (Subtype.ext h0)) }
  have hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) g := by ext k; rfl
  have hyF : coeffMap A.subtype y ∈ modularFunctionFieldBar M' := by
    rw [hy]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg
  obtain ⟨h, hresy⟩ := hR₀ y hyF
  have helt : (⟨coeffMap A.subtype y, hyF⟩ : ↥(modularFunctionFieldBar M')) = ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :=
    Subtype.ext hy
  have hres0 : ∀ k : ℤ, IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff k), hint k⟩ = 0 := by
    intro k
    have e : ((R₀.residue ⟨_, hgi⟩ : (modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y := by
      rw [← hresy]; congr 2
    rw [hres, ZeroMemClass.coe_zero] at e
    have := congrArg (fun s : LaurentSeries (ResidueField ↥A) => s.coeff k) e
    simp only [HahnSeries.coeff_zero, coeffMap_coeff] at this
    exact this.symm

  set g' : LaurentSeries ℚ := HahnSeries.C ((q : ℚ)⁻¹) * g with hg'def
  have hCmem : ∀ r : ℚ, HahnSeries.C r ∈ modularFunctionFieldFull M' := fun r => by
    rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; exact (modularFunctionFieldFull M').algebraMap_mem r
  have hg'F : g' ∈ modularFunctionFieldFull M' := by rw [hg'def]; exact mul_mem (hCmem _) hg
  have hg'coeff : ∀ k : ℤ, g'.coeff k = g.coeff k / q := by
    intro k; rw [hg'def, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, div_eq_inv_mul]
  have hg'int : ∀ k : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g'.coeff k) ∈ A := by
    intro k; rw [hg'coeff]
    exact div_mem_of_residue_eq_zero A q (g.coeff k) (hint k) (hres0 k)
  let y' : LaurentSeries ↥A :=
    { coeff := fun k => ⟨(coeffEmb (AlgebraicClosure ℚ) g').coeff k, hg'int k⟩
      isPWO_support' := (coeffEmb (AlgebraicClosure ℚ) g').isPWO_support'.mono (by
        intro k hk
        simp only [Function.mem_support, ne_eq] at hk ⊢
        exact fun h0 => hk (Subtype.ext h0)) }
  have hy' : coeffMap A.subtype y' = coeffEmb (AlgebraicClosure ℚ) g' := by ext k; rfl
  have hy'F : coeffMap A.subtype y' ∈ modularFunctionFieldBar M' := by
    rw [hy']; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F
  obtain ⟨hg'i0, -⟩ := hR₀ y' hy'F
  have hg'i : (⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by
    have helt' : (⟨coeffMap A.subtype y', hy'F⟩ : ↥(modularFunctionFieldBar M')) = ⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ :=
      Subtype.ext hy'
    exact helt' ▸ hg'i0

  have eBar : (⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ : ↥(modularFunctionFieldBar M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((q : (AlgebraicClosure ℚ))⁻¹) * ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ := by
    apply Subtype.ext
    show coeffEmb (AlgebraicClosure ℚ) g' = _
    rw [IntermediateField.coe_mul, SubalgebraClass.coe_algebraMap, algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply,
      hg'def, map_mul]
    congr 1
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (HahnSeries.C ((q : ℚ)⁻¹)) = _
    rw [show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (HahnSeries.C ((q : ℚ)⁻¹)) = HahnSeries.C (algebraMap ℚ (AlgebraicClosure ℚ) ((q : ℚ)⁻¹)) from
      HahnSeries.map_C _ _, map_inv₀, map_natCast]
  have hg'cusp : (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) := by
    intro P hP
    have hmem : (⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ : ↥(modularFunctionFieldBar M')) ∈ P.toValuationSubring := by
      rw [eBar]
      refine mul_mem (P.algebraMap_mem' _) ?_
      by_cases h0 : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) = 0
      · rw [h0]; exact zero_mem _
      · exact (P.mem_iff_ord_nonneg h0).mpr (hcusp P hP)
    by_cases h0 : (⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'F⟩ : ↥(modularFunctionFieldBar M')) = 0
    · rw [h0, Place.ord_zero]
    · exact (P.mem_iff_ord_nonneg h0).mp hmem

  refine ⟨g', hg'F, ?_, hg'i, hg'cusp⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqp.ne_zero
  rw [hg'def, ← HahnSeries.C_mul_eq_smul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul]

end S_ModularCurve_FullLevel_exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular (solution)
