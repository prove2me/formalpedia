-- Prove2me | solution 1 for N25.unitSeries25_normalization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:54.091563+00:00
-- url     : https://prove2.me/submissions/3e1c920c-ac2d-4680-8247-25516dbffd17

import Mathlib
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

open ModularCurve

namespace N25

private theorem residue_constant (g : ℕ) (hg : 0 < g) (hg25 : g < 25) :
    PowerSeries.constantCoeff (etaResidueSeries25 g) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [etaResidueSeries25, PowerSeries.coeff_mk, zero_add,
    Finset.range_one, Finset.prod_singleton, mul_zero, zero_add, zero_add, mul_one]
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  simp [map_mul, map_sub, map_pow, Nat.ne_of_gt hg,
    Nat.ne_of_gt (Nat.sub_pos_of_lt hg25)]

private theorem pair_constant (i : Fin 5) :
    PowerSeries.constantCoeff (unitPairSeries25 i) = 1 := by
  have bounds : ∀ i : Fin 5,
      0 < (unitResidues25 i).1 ∧ (unitResidues25 i).1 < 25 ∧
      0 < (unitResidues25 i).2 ∧ (unitResidues25 i).2 < 25 := by
    intro i
    fin_cases i <;> norm_num [unitResidues25]
  rw [unitPairSeries25, map_mul,
    residue_constant _ (bounds i).1 (bounds i).2.1,
    residue_constant _ (bounds i).2.2.1 (bounds i).2.2.2, one_mul]

private theorem shifted_series (K : Type*) [Field K]
    (p : PowerSeries ℤ) (hp : PowerSeries.constantCoeff p = 1) (n : ℕ) :
    let f := intSeriesC K (PowerSeries.X ^ n * p)
    f ≠ 0 ∧ f.order = (n : ℤ) ∧ f.coeff (n : ℤ) = 1 := by
  dsimp only
  have hform : intSeriesC K (PowerSeries.X ^ n * p) =
      HahnSeries.single (n : ℤ) 1 * intSeriesC K p := by
    simp [intSeriesC, map_mul, map_pow]
  have hc : (intSeriesC K p).coeff 0 = 1 := by
    change (HahnSeries.ofPowerSeries ℤ K (p.map (Int.castRingHom K))).coeff (0 : ℕ) = 1
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hp]
    simp
  have hn : (intSeriesC K (PowerSeries.X ^ n * p)).coeff (n : ℤ) = 1 := by
    rw [hform, HahnSeries.coeff_single_mul, sub_self, hc, one_mul]
  have hz : intSeriesC K (PowerSeries.X ^ n * p) ≠ 0 := by
    intro h
    simpa [h] using hn
  refine ⟨hz, le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [hn]; exact one_ne_zero)) ?_, hn⟩
  by_contra h
  have hlt : (intSeriesC K (PowerSeries.X ^ n * p)).order < (n : ℤ) := lt_of_not_ge h
  have hc0 : (intSeriesC K (PowerSeries.X ^ n * p)).coeff
      (intSeriesC K (PowerSeries.X ^ n * p)).order = 0 := by
    nth_rw 1 [hform]
    rw [HahnSeries.coeff_single_mul]
    change 1 * (HahnSeries.ofPowerSeries ℤ K (p.map (Int.castRingHom K))).coeff _ = 0
    rw [ofPowerSeries_coeff_of_neg _ (sub_neg.mpr hlt), mul_zero]
  exact (HahnSeries.coeff_order_eq_zero.not.mpr hz) hc0

/-- The frozen integral ratios have the specified orders and leading coefficient in every field. -/
theorem _root_.solution (K : Type*) [Field K] :
    intSeriesC K unitDenominatorSeries25 ≠ 0 ∧
      ∀ i : Fin 5, (unitSeries25 K i).order = unitQOrder25 i ∧
        (unitSeries25 K i).coeff (unitQOrder25 i) = 1 := by
  have hd := shifted_series K (dedekindEtaUnit ^ 3)
    (by simp [constantCoeff_dedekindEtaUnit]) 3
  have hde : unitDenominatorSeries25 = PowerSeries.X ^ 3 * dedekindEtaUnit ^ 3 := by
    simp only [unitDenominatorSeries25, mul_pow]
  rw [← hde] at hd
  refine ⟨hd.1, ?_⟩
  intro i
  let p := dedekindEtaUnit ^ 3 * unitPairSeries25 i *
    (unitPairSeries25 (i + 1)).invOfUnit (1 : ℤˣ)
  have hp : PowerSeries.constantCoeff p = 1 := by
    simp [p, map_mul, map_pow, constantCoeff_dedekindEtaUnit,
      pair_constant, PowerSeries.constantCoeff_invOfUnit]
  have hn := shifted_series K p hp (3 + unitQOrder25 i).toNat
  have hne : unitNumeratorSeries25 i = PowerSeries.X ^ (3 + unitQOrder25 i).toNat * p := by
    simp only [unitNumeratorSeries25, p, mul_assoc]
  rw [← hne] at hn
  have hnonneg : 0 ≤ 3 + unitQOrder25 i := by
    fin_cases i <;> norm_num [unitQOrder25]
  have hnat : ((3 + unitQOrder25 i).toNat : ℤ) = 3 + unitQOrder25 i :=
    Int.toNat_of_nonneg hnonneg
  have ho : (unitSeries25 K i).order = unitQOrder25 i := by
    rw [unitSeries25, order_div_of_ne_zero_bar hn.1 hd.1, hn.2.1, hd.2.1, hnat]
    omega
  refine ⟨ho, ?_⟩
  have heq : unitSeries25 K i * intSeriesC K unitDenominatorSeries25 =
      intSeriesC K (unitNumeratorSeries25 i) := div_mul_cancel₀ _ hd.1
  have hc := HahnSeries.coeff_mul_order_add_order (unitSeries25 K i)
    (intSeriesC K unitDenominatorSeries25)
  rw [heq, HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq,
    ho, hd.2.1, hd.2.2, mul_one] at hc
  have hindex : unitQOrder25 i + (3 : ℤ) = ((3 + unitQOrder25 i).toNat : ℤ) := by
    omega
  exact hc.symm.trans ((congrArg
    (intSeriesC K (unitNumeratorSeries25 i)).coeff hindex).trans hn.2.2)

end N25
