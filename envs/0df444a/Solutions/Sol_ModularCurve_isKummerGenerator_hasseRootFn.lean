-- Prove2me | solution 1 for ModularCurve.isKummerGenerator_hasseRootFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/19d55439-9c57-5bb2-a853-f489ae4e957e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isKummerGenerator_hasseRootFn

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open scoped MatrixGroups

namespace KumGenE95

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) :
    (1 : ℝ) ∈ (Δ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

theorem isIntegralQExp_pow {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) {k : ℤ}
    (f : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k) {pf : PowerSeries ℤ} (hf : IsIntegralQExp f pf)
    (n : ℕ) : IsIntegralQExp (f.pow n) (pf ^ n) := by
  rw [IsIntegralQExp, map_pow, hf]
  exact (ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods hT) f n).symm

theorem isIntegralQExp_mcast {Γ : Subgroup (GL (Fin 2) ℝ)} {a b : ℤ} (h : a = b) (f : ModularForm Γ a)
    {pf : PowerSeries ℤ} (hf : IsIntegralQExp f pf) : IsIntegralQExp (ModularForm.mcast h f) pf := by
  rw [IsIntegralQExp, ModularForm.coe_mcast]
  exact hf

theorem intSeriesC_pow (K : Type*) [Field K] (q : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  simp [intSeriesC]

end KumGenE95

open KumGenE95 in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p]
    (M : ℕ) [NeZero M] (w : ModularCurve.IntegralWeightOneForm κ M) :
    ModularCurve.IgusaCover.IsKummerGenerator (p - 1) (ModularCurve.x1FunctionFieldC κ M) w.hasseRootFn := by
  have hp : p.Prime := Fact.out
  refine ⟨by omega, w.hasseRootFn_ne_zero, ?_⟩

  obtain ⟨A, b, hAb, hb0, hbn⟩ :=
    ModularForm.exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le p hp hp5 M
  have hle : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_in_Gamma0 M)
  let A1 : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ((p : ℤ) - 1) :=
    restrictForm hle A
  let pf : PowerSeries ℤ := PowerSeries.mk b
  have hA1 : IsIntegralQExp A1 pf := by
    rw [isIntegralQExp_iff]
    intro n
    rw [PowerSeries.coeff_mk, coe_restrictForm]
    exact (hAb n).symm
  have hpf : intSeriesC κ pf = 1 := by
    have hmap : pf.map (Int.castRingHom κ) = 1 := by
      ext n
      rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_one, eq_intCast]
      split_ifs with hn
      · subst hn
        have h0 : ((b 0 - 1 : ℤ) : κ) = 0 := (CharP.intCast_eq_zero_iff κ p _).2 hb0
        rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at h0
        exact h0
      · exact (CharP.intCast_eq_zero_iff κ p _).2 (hbn n (Nat.pos_of_ne_zero hn))
    simp [intSeriesC, hmap]

  have hwt : ((p - 1 : ℕ) : ℤ) * 1 = (p : ℤ) - 1 := by
    rw [mul_one, Nat.cast_sub hp.one_le, Nat.cast_one]
  let g : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ((p : ℤ) - 1) :=
    ModularForm.mcast hwt (w.form.pow (p - 1))
  have hg : IsIntegralQExp g (w.series ^ (p - 1)) :=
    isIntegralQExp_mcast hwt _ (isIntegralQExp_pow (T_mem_Gamma1 M) w.form w.isIntegralQExp (p - 1))
  have hg0 : intSeriesC κ (w.series ^ (p - 1)) ≠ 0 := by
    rw [intSeriesC_pow]
    exact pow_ne_zero _ w.intSeriesC_ne_zero

  have key : w.hasseRootFn ^ (p - 1) = intSeriesC κ pf / intSeriesC κ (w.series ^ (p - 1)) := by
    rw [hpf, intSeriesC_pow, one_div, IntegralWeightOneForm.hasseRootFn, inv_pow]
  rw [key]
  exact div_mem_qExpFunctionFieldC A1 g hA1 hg hg0

end S_ModularCurve_isKummerGenerator_hasseRootFn
end P2MW
export P2MW.S_ModularCurve_isKummerGenerator_hasseRootFn (solution)
