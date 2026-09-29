-- Prove2me | solution 1 for ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/40db9a97-a92f-5459-8577-9bbdbd7c9546

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "TwoChart.chartAlg TwoChart.mem_chartAlg_iff TwoChart.chartAlgFin TwoChart.chartAlgInf qExpFunctionFieldC jNum constantCoeff_jNum jq coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange jqModC jqModC_rat map_jqModC exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective"
p2m_open "ModularCurve"
namespace IntCoeffLBC

theorem ofPowerSeries_coeff_int {A : Type*} [CommRing A] (x : PowerSeries A) (k : ℤ) :
    (HahnSeries.ofPowerSeries ℤ A x).coeff k = if 0 ≤ k then PowerSeries.coeff k.toNat x else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Int.toNat_natCast, HahnSeries.ofPowerSeries_apply_coeff]
  · rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    rintro ⟨n, hn⟩
    apply h
    rw [← hn]
    exact Int.natCast_nonneg n

theorem coeffMap_intSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : PowerSeries ℤ) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R (x.map (Int.castRingHom R))) =
      HahnSeries.ofPowerSeries ℤ S (x.map (Int.castRingHom S)) := by
  ext k
  rw [coeffMap_coeff, ofPowerSeries_coeff_int, ofPowerSeries_coeff_int]
  split_ifs
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · exact map_zero f

theorem coeffMap_injective' {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun x y h => by
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem exists_mul_coeffMap_eq_of_mem {R : Type*} [CommRing R] (φ : R →+* ℚ) (Γ : Subgroup SL(2, ℤ))
    {x : LaurentSeries ℚ} (hx : x ∈ qExpFunctionFieldC ℚ Γ) :
    ∃ a b : LaurentSeries R, coeffMap φ b ≠ 0 ∧ x * coeffMap φ b = coeffMap φ a := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, f, g, pf, pg, -, -, hg0, rfl⟩ := hx
    refine ⟨HahnSeries.ofPowerSeries ℤ R (pf.map (Int.castRingHom R)),
      HahnSeries.ofPowerSeries ℤ R (pg.map (Int.castRingHom R)), ?_, ?_⟩
    · rw [coeffMap_intSeries]
      exact hg0
    · rw [coeffMap_intSeries, coeffMap_intSeries]
      exact div_mul_cancel₀ _ hg0
  | algebraMap c =>
    have hinj : Function.Injective (algebraMap ℚ (LaurentSeries ℚ)) := (algebraMap ℚ (LaurentSeries ℚ)).injective
    refine ⟨(c.num : LaurentSeries R), (c.den : LaurentSeries R), ?_, ?_⟩
    · rw [map_natCast, ← map_natCast (algebraMap ℚ (LaurentSeries ℚ)), map_ne_zero_iff _ hinj]
      exact Nat.cast_ne_zero.mpr c.den_ne_zero
    · rw [map_natCast, map_intCast, ← map_natCast (algebraMap ℚ (LaurentSeries ℚ)),
        ← map_intCast (algebraMap ℚ (LaurentSeries ℚ)), ← map_mul, Rat.mul_den_eq_num]
  | add x y hx hy ihx ihy =>
    obtain ⟨a₁, b₁, hb₁, h₁⟩ := ihx
    obtain ⟨a₂, b₂, hb₂, h₂⟩ := ihy
    refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hb₁ hb₂
    · rw [map_mul, map_add, map_mul, map_mul, ← h₁, ← h₂]; ring
  | inv x hx ihx =>
    obtain ⟨a, b, hb, h⟩ := ihx
    by_cases ha : coeffMap φ a = 0
    · have hx0 : x = 0 := by
        rcases mul_eq_zero.mp (h.trans ha) with h0 | h0
        · exact h0
        · exact absurd h0 hb
      refine ⟨0, 1, ?_, ?_⟩
      · rw [map_one]; exact one_ne_zero
      · rw [hx0, inv_zero, zero_mul, map_zero]
    · refine ⟨b, a, ha, ?_⟩
      have hx0 : x ≠ 0 := fun h0 => ha (by rw [← h, h0, zero_mul])
      rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  | mul x y hx hy ihx ihy =>
    obtain ⟨a₁, b₁, hb₁, h₁⟩ := ihx
    obtain ⟨a₂, b₂, hb₂, h₂⟩ := ihy
    refine ⟨a₁ * a₂, b₁ * b₂, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hb₁ hb₂
    · rw [map_mul, map_mul, ← h₁, ← h₂]; ring

section FracL

variable (A : Type*) [CommRing A] [IsDomain A] (L : Type*) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L]
  (Γ : Subgroup SL(2, ℤ))

theorem coeffMap_algebraMap_coeffMap_intCast (a : LaurentSeries ℤ) :
    coeffMap (algebraMap A L) (coeffMap (Int.castRingHom A) a) = coeffEmb L (coeffMap (Int.castRingHom ℚ) a) := by
  rw [coeffEmb, coeffMap_coeffMap, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) a

theorem exists_mul_coeffMap_eq_of_mem_laurentBaseChange
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) :
    ∃ a b : LaurentSeries A, coeffMap (algebraMap A L) b ≠ 0 ∧ x * coeffMap (algebraMap A L) b = coeffMap (algebraMap A L) a := by
  have hφ : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hemb : Function.Injective (coeffEmb L) := coeffMap_injective' (algebraMap ℚ L).injective
  change x ∈ IntermediateField.adjoin L _ at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨a, b, hb, h⟩ := exists_mul_coeffMap_eq_of_mem (Int.castRingHom ℚ) Γ hf
    refine ⟨coeffMap (Int.castRingHom A) a, coeffMap (Int.castRingHom A) b, ?_, ?_⟩
    · rw [coeffMap_algebraMap_coeffMap_intCast, map_ne_zero_iff _ hemb]
      exact hb
    · rw [coeffMap_algebraMap_coeffMap_intCast, coeffMap_algebraMap_coeffMap_intCast, ← map_mul, h]
  | algebraMap c =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hb0 : algebraMap A L b ≠ 0 := (map_ne_zero_iff _ hφ).mpr (nonZeroDivisors.ne_zero hb)
    refine ⟨HahnSeries.single 0 a, HahnSeries.single 0 b, ?_, ?_⟩
    · rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single, map_ne_zero_iff _ (algebraMap L (LaurentSeries L)).injective]
      exact hb0
    · rw [coeffMap_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single, ← algebraMap_laurentSeries_eq_single,
        ← map_mul, div_mul_cancel₀ _ hb0]
  | add x y hx hy ihx ihy =>
    obtain ⟨a₁, b₁, hb₁, h₁⟩ := ihx
    obtain ⟨a₂, b₂, hb₂, h₂⟩ := ihy
    refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hb₁ hb₂
    · rw [map_mul, map_add, map_mul, map_mul, ← h₁, ← h₂]; ring
  | inv x hx ihx =>
    obtain ⟨a, b, hb, h⟩ := ihx
    by_cases ha : coeffMap (algebraMap A L) a = 0
    · have hx0 : x = 0 := by
        rcases mul_eq_zero.mp (h.trans ha) with h0 | h0
        · exact h0
        · exact absurd h0 hb
      refine ⟨0, 1, ?_, ?_⟩
      · rw [map_one]; exact one_ne_zero
      · rw [hx0, inv_zero, zero_mul, map_zero]
    · refine ⟨b, a, ha, ?_⟩
      have hx0 : x ≠ 0 := fun h0 => ha (by rw [← h, h0, zero_mul])
      rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  | mul x y hx hy ihx ihy =>
    obtain ⟨a₁, b₁, hb₁, h₁⟩ := ihx
    obtain ⟨a₂, b₂, hb₂, h₂⟩ := ihy
    refine ⟨a₁ * a₂, b₁ * b₂, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hb₁ hb₂
    · rw [map_mul, map_mul, ← h₁, ← h₂]; ring

end FracL

section Key

universe u

variable (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  (L : Type u) [Field L] [Algebra A L]
  (K : IntermediateField L (LaurentSeries L)) [Algebra A ↥K] [IsScalarTower A L ↥K]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem key (hφ : Function.Injective (algebraMap A L))
    (hfrac : ∀ x : ↥K, ∃ a c : LaurentSeries A, coeffMap (algebraMap A L) c ≠ 0 ∧
      (x : LaurentSeries L) * coeffMap (algebraMap A L) c = coeffMap (algebraMap A L) a)
    (s : Set ↥K)
    (hs : ∀ z ∈ s, ∃ w : LaurentSeries A, coeffMap (algebraMap A L) w = ((z : ↥K) : LaurentSeries L))
    (b : ↥K) (hb : b ∈ ModularCurve.TwoChart.chartAlg A (↥K) s) :
    ∃ y : LaurentSeries A, coeffMap (algebraMap A L) y = ((b : ↥K) : LaurentSeries L) := by
  let φL : LaurentSeries A →+* LaurentSeries L := coeffMap (algebraMap A L)
  have hφL : Function.Injective φL := coeffMap_injective' hφ
  let ψ0 : ↥K →+* LaurentSeries L := algebraMap ↥K (LaurentSeries L)
  have hψ0 : ∀ x : ↥K, ψ0 x = (x : LaurentSeries L) := fun x => rfl

  have hconst : ∀ r : A, ψ0 (algebraMap A ↥K r) = φL (HahnSeries.single (0 : ℤ) r) := fun r => by
    rw [IsScalarTower.algebraMap_apply A L ↥K, hψ0]
    show algebraMap ↥K (LaurentSeries L) (algebraMap L ↥K (algebraMap A L r)) = _
    rw [← IsScalarTower.algebraMap_apply L ↥K (LaurentSeries L), algebraMap_laurentSeries_eq_single]
    exact (coeffMap_single (algebraMap A L) 0 r).symm

  have hrange : ∀ z ∈ Algebra.adjoin A s, ψ0 z ∈ φL.range := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨w, hw⟩ := hs z hz
      exact ⟨w, hw⟩
    | algebraMap r => exact ⟨_, (hconst r).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

  let e : LaurentSeries A ≃+* ↥φL.range :=
    RingEquiv.ofBijective φL.rangeRestrict
      ⟨fun x y h => hφL (congrArg Subtype.val h), φL.rangeRestrict_surjective⟩
  have he : ∀ w : ↥φL.range, φL (e.symm w) = (w : LaurentSeries L) := fun w => by
    have h1 : ((e (e.symm w) : ↥φL.range) : LaurentSeries L) = φL (e.symm w) := rfl
    rw [← h1, e.apply_symm_apply]
  let θ : ↥(Algebra.adjoin A s) →+* LaurentSeries A :=
    e.symm.toRingHom.comp ((ψ0.comp (Algebra.adjoin A s).val.toRingHom).codRestrict φL.range
      (fun z => hrange z z.2))
  have hθ : ∀ z : ↥(Algebra.adjoin A s), φL (θ z) = ψ0 z := fun z => he _

  rw [ModularCurve.TwoChart.mem_chartAlg_iff] at hb
  obtain ⟨P₀, hP₀m, hP₀⟩ := hb
  have hint : φL.IsIntegralElem ((b : ↥K) : LaurentSeries L) := by
    refine ⟨P₀.map θ, hP₀m.map θ, ?_⟩
    have hcomp : φL.comp θ = ψ0.comp (algebraMap ↥(Algebra.adjoin A s) ↥K) := RingHom.ext fun z => hθ z
    rw [Polynomial.eval₂_map, hcomp]
    show Polynomial.eval₂ (ψ0.comp (algebraMap ↥(Algebra.adjoin A s) ↥K)) (ψ0 b) P₀ = 0
    rw [← Polynomial.hom_eval₂, hP₀, map_zero]

  obtain ⟨a, c, hc, hac⟩ := hfrac b
  have hfrac' : ∃ a' c' : LaurentSeries A, c' ≠ 0 ∧
      ((b : ↥K) : LaurentSeries L) = coeffMap (algebraMap A L) a' / coeffMap (algebraMap A L) c' :=
    ⟨a, c, fun h0 => hc (by rw [h0, map_zero]), by rw [eq_div_iff hc]; exact hac⟩
  exact exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective (algebraMap A L) hφ _ hfrac' hint

end Key

section J

variable (A : Type*) [CommRing A]

theorem isUnit_jqModC : IsUnit (jqModC A) := by
  unfold jqModC
  refine IsUnit.mul ?_ (IsUnit.map (HahnSeries.ofPowerSeries ℤ A) ?_)
  · refine IsUnit.of_mul_eq_one (HahnSeries.single (1 : ℤ) (1 : A)) ?_
    rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, HahnSeries.single_zero_one]
  · rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]
    exact isUnit_one

theorem coeffMap_jqModC {B : Type*} [CommRing B] (f : A →+* B) : coeffMap f (jqModC A) = jqModC B := map_jqModC f

end J

end IntCoeffLBC
end ModularCurve

open ModularCurve.IntCoeffLBC in
theorem solution
    (Γ : Subgroup SL(2, ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ∃ y : LaurentSeries A,
        ModularCurve.coeffMap (algebraMap A L) y = ((b : ↥K) : LaurentSeries L)) ∧
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ∃ y : LaurentSeries A,
        ModularCurve.coeffMap (algebraMap A L) y = ((b : ↥K) : LaurentSeries L)) := by
  have hφ : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

  have hfrac : ∀ x : ↥K, ∃ a c : LaurentSeries A, coeffMap (algebraMap A L) c ≠ 0 ∧
      (x : LaurentSeries L) * coeffMap (algebraMap A L) c = coeffMap (algebraMap A L) a := fun x =>
    exists_mul_coeffMap_eq_of_mem_laurentBaseChange A L Γ (hK ▸ x.2)

  have hjA : coeffMap (algebraMap A L) (jqModC A) = ((j : ↥K) : LaurentSeries L) := by
    rw [hj, coeffMap_jqModC, ← jqModC_rat, coeffEmb]
    exact (coeffMap_jqModC ℚ (algebraMap ℚ L)).symm
  obtain ⟨uu, huu⟩ := isUnit_jqModC A
  have hjA' : coeffMap (algebraMap A L) (↑uu⁻¹ : LaurentSeries A) = (((j : ↥K)⁻¹ : ↥K) : LaurentSeries L) := by
    rw [map_units_inv, huu, hjA]
    rfl
  refine ⟨fun b => key A L K hφ hfrac {j} ?_ b b.2, fun b => key A L K hφ hfrac {(j : ↥K)⁻¹} ?_ b b.2⟩
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact ⟨jqModC A, hjA⟩
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact ⟨_, hjA'⟩

#print axioms solution

end S_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange (solution)
