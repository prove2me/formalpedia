-- Prove2me | solution 1 for ModularCurve.mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d93803c1-8857-5875-b232-0ef84feb1bcd

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "TwoChart.chartAlgInf qExpFunctionFieldC jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange jqModC jqModC_rat map_jqModC exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange"
p2m_open "ModularCurve"
namespace QExpInf

variable {L : Type} [Field L] [CharZero L]
variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]

abbrev psL (L : Type) [Field L] {A : Type} [CommRing A] [Algebra A L] (x : PowerSeries A) : LaurentSeries L :=
  HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))

theorem psL_one : psL L (1 : PowerSeries A) = 1 := by simp [psL]

theorem psL_mul (x y : PowerSeries A) : psL L (x * y) = psL L x * psL L y := by simp [psL]

theorem map_map_ps {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T] (f : R →+* S) (g : S →+* T)
    (x : PowerSeries R) : (x.map f).map g = x.map (g.comp f) := by
  ext n
  simp only [PowerSeries.coeff_map, RingHom.comp_apply]

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Y : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R Y) = HahnSeries.ofPowerSeries ℤ S (Y.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg Y hk, ofPowerSeries_coeff_of_neg (Y.map f) hk, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem exists_powerSeries_of_forall_coeff_neg_eq_zero {R : Type*} [CommRing R] (y : LaurentSeries R)
    (hy : ∀ n : ℤ, n < 0 → y.coeff n = 0) :
    ∃ Y : PowerSeries R, HahnSeries.ofPowerSeries ℤ R Y = y := by
  refine ⟨PowerSeries.mk fun n => y.coeff n, HahnSeries.ext (funext fun k => ?_)⟩
  rcases lt_or_ge k 0 with hk | hk
  · rw [hy k hk]
    exact ofPowerSeries_coeff_of_neg (PowerSeries.mk fun n => y.coeff n) hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

theorem single_one_mul_jqModC (L : Type) [Field L] :
    HahnSeries.single (1 : ℤ) (1 : L) * jqModC L = HahnSeries.ofPowerSeries ℤ L (jNum.map (Int.castRingHom L)) := by
  rw [jqModC, ← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel, one_mul]
  exact one_mul _

theorem jqModC_ne_zero (L : Type) [Field L] : jqModC L ≠ 0 := by
  intro h
  have h1 := single_one_mul_jqModC L
  rw [h, mul_zero] at h1
  have := congrArg PowerSeries.constantCoeff (HahnSeries.ofPowerSeries_injective (h1.symm.trans (map_zero _).symm))
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one, map_zero] at this
  exact one_ne_zero this

section Frame

variable (K : IntermediateField L (LaurentSeries L)) [Algebra A ↥K] [IsScalarTower A L ↥K]
variable (j : ↥K) (hj : ((j : LaurentSeries L)) = coeffEmb L jq) [Fact (j ≠ 0)]
variable (W₀ : ValuationSubring ↥K)
  (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
    (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

include hj in
theorem coe_j_eq : ((j : ↥K) : LaurentSeries L) = jqModC L := by
  rw [hj, coeffEmb, ← jqModC_rat]
  exact map_jqModC _

theorem jNum_mapA_map : (jNum.map (Int.castRingHom A)).map (algebraMap A L) = jNum.map (Int.castRingHom L) := by
  rw [map_map_ps, RingHom.ext_int ((algebraMap A L).comp (Int.castRingHom A)) (Int.castRingHom L)]

theorem jNum_mapA_residue_ne_zero : (jNum.map (Int.castRingHom A)).map (IsLocalRing.residue A) ≠ 0 := by
  rw [map_map_ps]
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one, map_zero] at this
  exact one_ne_zero this

include hW₀ in

theorem algebraMap_mem (a : A) : algebraMap A ↥K a ∈ W₀ := by
  rw [hW₀]
  refine ⟨PowerSeries.C a, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
  rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
  rw [IsScalarTower.algebraMap_apply A L ↥K a]
  change algebraMap L (LaurentSeries L) (algebraMap A L a) = _
  rw [algebraMap_laurentSeries_eq_single]
  rfl

include hj hW₀ in

theorem inv_j_mem : (j⁻¹ : ↥K) ∈ W₀ := by
  rw [hW₀]
  refine ⟨PowerSeries.X, jNum.map (Int.castRingHom A), jNum_mapA_residue_ne_zero, ?_⟩
  rw [jNum_mapA_map, PowerSeries.map_X, HahnSeries.ofPowerSeries_X, ← single_one_mul_jqModC, ← coe_j_eq K j hj]
  push_cast
  rw [mul_left_comm, inv_mul_cancel₀ ((coe_j_eq K j hj) ▸ jqModC_ne_zero L), mul_one]

include hj hW₀ in

theorem j_mem : (j : ↥K) ∈ W₀ := by
  rw [hW₀]
  refine ⟨jNum.map (Int.castRingHom A), PowerSeries.X, by rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero, ?_⟩
  rw [jNum_mapA_map, PowerSeries.map_X, HahnSeries.ofPowerSeries_X, ← single_one_mul_jqModC, ← coe_j_eq K j hj, mul_comm]

include hj hW₀ in

theorem adjoin_subset (x : ↥K) (hx : x ∈ Algebra.adjoin A ({j⁻¹} : Set ↥K)) : x ∈ W₀ := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact inv_j_mem K j hj W₀ hW₀
  | algebraMap r => exact algebraMap_mem K W₀ hW₀ r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

include hj hW₀ in

theorem coe_mem (b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) : ((b : ↥K)) ∈ W₀ := by
  have hb : IsIntegral (Algebra.adjoin A ({j⁻¹} : Set ↥K)) (b : ↥K) := b.2
  let φ : ↥(Algebra.adjoin A ({j⁻¹} : Set ↥K)) →+* ↥W₀ :=
    (algebraMap ↥(Algebra.adjoin A ({j⁻¹} : Set ↥K)) ↥K).codRestrict W₀.toSubring
      (fun x => adjoin_subset K j hj W₀ hW₀ x x.2)
  have hcomp : (algebraMap ↥W₀ ↥K).comp φ = (RingHom.id ↥K).comp (algebraMap _ ↥K) :=
    RingHom.ext fun _ => rfl
  have hint : IsIntegral ↥W₀ (b : ↥K) := hb.map_of_comp_eq φ (RingHom.id ↥K) hcomp
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W₀) (K := ↥K)).mp hint
  rw [← hy]
  exact y.2

end Frame

end QExpInf
end ModularCurve

open ModularCurve.QExpInf in
theorem solution
    (Γ : Subgroup SL(2, ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (ψ : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A)
    (hψ0 : ∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
      algebraMap A L (ψ f) = (((f : ↥K) : LaurentSeries L)).coeff 0)
    (hord : ∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ∀ k : ℤ, k < 0 →
      (((f : ↥K) : LaurentSeries L)).coeff k = 0) :
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ((b : ↥K)) ∈ W₀) ∧
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ((b : ↥K)) ∈ W₀.nonunits →
      ψ b ∈ IsLocalRing.maximalIdeal A) := by
  have hφ : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  refine ⟨fun b => coe_mem K j hj W₀ hW₀ b, fun b hbn => ?_⟩

  obtain ⟨y, hy⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange Γ L K hK A j hj).2 b
  have hneg : ∀ n : ℤ, n < 0 → y.coeff n = 0 := by
    intro n hn
    have h := hord b n hn
    rw [← hy, coeffMap_coeff] at h
    exact hφ (by rw [h, map_zero])
  obtain ⟨Y, hY⟩ := exists_powerSeries_of_forall_coeff_neg_eq_zero y hneg
  have hbY : ((b : ↥K) : LaurentSeries L) = psL L Y := by
    rw [← hy, ← hY, coeffMap_ofPowerSeries]

  have hψb : ψ b = PowerSeries.constantCoeff Y := by
    apply hφ
    rw [hψ0, hbY, psL, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff]

  by_contra hnot
  have hu : IsUnit (PowerSeries.constantCoeff Y) := by
    rw [← hψb]; exact (IsLocalRing.notMem_maximalIdeal.mp hnot)
  obtain ⟨u, hu⟩ := hu
  have hb0 : ((b : ↥K) : LaurentSeries L) ≠ 0 := by
    intro h0
    have hps : psL L Y = 0 := by rw [← hbY, h0]
    have hY0 : Y.map (algebraMap A L) = 0 := HahnSeries.ofPowerSeries_injective (hps.trans (map_zero _).symm)
    have : algebraMap A L (PowerSeries.constantCoeff Y) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_map, hY0, map_zero]
    rw [← hu, map_eq_zero_iff _ hφ] at this
    exact u.ne_zero this
  have hb0' : (b : ↥K) ≠ 0 := fun h => hb0 (by rw [h]; rfl)
  have hinv : ((b : ↥K))⁻¹ ∈ W₀ := by
    rw [hW₀]
    refine ⟨1, Y, ?_, ?_⟩
    · intro h0
      have := congrArg PowerSeries.constantCoeff h0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
        ← hu, map_zero] at this
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr u.isUnit this
    · rw [map_one, map_one]
      push_cast
      rw [hbY, inv_mul_cancel₀ (hbY ▸ hb0)]

  have hmem : (b : ↥K) ∈ W₀ := coe_mem K j hj W₀ hW₀ b
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hbn
  obtain ⟨hmem', hmax⟩ := hbn
  apply (IsLocalRing.mem_maximalIdeal _).mp hmax
  refine IsUnit.of_mul_eq_one ⟨((b : ↥K))⁻¹, hinv⟩ (Subtype.ext ?_)
  show (b : ↥K) * ((b : ↥K))⁻¹ = 1
  exact mul_inv_cancel₀ hb0'

#print axioms solution

end
end S_ModularCurve_mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange (solution)
