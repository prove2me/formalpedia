-- Prove2me | solution 1 for GlobalTheory.UnitCase.mvExp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:21.942857+00:00
-- url     : https://prove2.me/submissions/5ef03cb6-197b-4e32-a477-a1bad720d0fb

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_coeff_mul_pow_eq_zero
import Theorems.Thm_GlobalTheory_UnitCase_coeff_mvExp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution [CharZero C] {a b : MvPowerSeries σ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : mvExp (a + b) = mvExp a * mvExp b := by
  classical
  ext m
  set N := m.degree + 1 with hN
  have hR : MvPowerSeries.coeff m (mvExp a * mvExp b) =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N,
        MvPowerSeries.coeff m (a ^ p.1 * b ^ p.2) / ((p.1.factorial : C) * p.2.factorial) := by
    rw [MvPowerSeries.coeff_mul]
    simp only [MvPowerSeries.coeff_mul, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hd : q.1.degree + q.2.degree = m.degree := by rw [← hq, map_add]
    rw [coeff_mvExp_eq ha q.1 N (by omega), coeff_mvExp_eq hb q.2 N (by omega),
      Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [div_mul_div_comm]
  rw [hR, coeff_mvExp_eq (by rw [map_add, ha, hb, add_zero]) m N (by omega)]
  rw [← Finset.sum_filter_of_ne (p := fun p : ℕ × ℕ => p.1 + p.2 ∈ Finset.range N)]
  · rw [← Finset.sum_fiberwise_eq_sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have : (Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => p.1 + p.2 = k) =
        Finset.HasAntidiagonal.antidiagonal k := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    rw [this, (Commute.all a b).add_pow', map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_nsmul, nsmul_eq_mul, ← hp, Nat.cast_add_choose C]
    have h1 : ((p.1 + p.2).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : ((p.1).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h3 : ((p.2).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  · intro p _ hp
    rw [Finset.mem_range]
    by_contra hc
    exact hp (by rw [coeff_mul_pow_eq_zero ha hb _ _ m (by omega), zero_div])
end GlobalTheory.UnitCase
