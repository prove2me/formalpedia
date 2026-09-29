-- Prove2me | solution 1 for ModularCurve.XOneP.divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/425809cb-8ae3-5e7f-a30d-72f0d036b7b4

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

namespace GalIsoX1ClassImpl

theorem pair_nsmul_left {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (e : DivisorialWeilPairingData K F n) (k : ℕ) (x y : Pic0.torsion K F n) :
    e.pair (k • x) y = e.pair x y ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, e.pair_zero_left]
  | succ k ih => rw [succ_nsmul, e.pair_add_left, ih, pow_succ]

theorem pair_sub_left {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (e : DivisorialWeilPairingData K F n) (x x' y : Pic0.torsion K F n) :
    e.pair (x - x') y = e.pair x y * (e.pair x' y)⁻¹ := by
  have h : e.pair (x - x') y * e.pair x' y = e.pair x y := by
    rw [← e.pair_add_left, sub_add_cancel]
  rw [← h, mul_assoc, mul_inv_cancel₀ (e.pair_ne_zero x' y), mul_one]

end GalIsoX1ClassImpl

set_option maxHeartbeats 1600000 in
open GalIsoX1ClassImpl in
theorem solution
    (N : ℕ) [NeZero N]
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (n : ℕ) [NeZero n] (hpn : ¬ p ∣ n)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N)]
    (W : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N) n)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ Pl.inertiaSubgroupIn ℚ)
    (z y x : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N) n)
    (hyσ : σ • (y : ModularCurve.JOne N) = y)
    (hx : (x : ModularCurve.JOne N) = σ • (z : ModularCurve.JOne N) - z) :
    W.pair x y = 1 := by
  classical

  let g : SemilinearAut (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar N) := arithmeticGalois (x1FunctionField N) σ
  have hg : ∀ u : JOne N, σ • u = g • u := fun u => rfl
  have hgy : g • y = y := Subtype.ext (by rw [SemilinearAut.coe_torsion_smul, ← hg]; exact hyσ)
  have hxg : x = g • z - z := Subtype.ext (by rw [hx, hg, AddSubgroupClass.coe_sub, SemilinearAut.coe_torsion_smul])

  have hζ : W.pair z y ^ n = 1 := by
    rw [← GalIsoX1ClassImpl.pair_nsmul_left]
    have : n • z = 0 := Subtype.ext (by
      rw [AddSubgroupClass.coe_nsmul, ZeroMemClass.coe_zero]
      have hz := z.2
      rw [Pic0.mem_torsion, natCast_zsmul] at hz
      exact hz)
    rw [this, W.pair_zero_left]
  have hp : p.Prime := Fact.out
  have hσζ : σ (W.pair z y) = W.pair z y :=
    ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one Pl hp hPl hσ hpn hζ
  have h1 : W.pair (g • z) y = σ (W.pair z y) := by
    conv_lhs => rw [← hgy]
    rw [AlgebraicCurve.DivisorialWeilPairingData.pair_semilinearSmul]
    rfl
  rw [hxg, GalIsoX1ClassImpl.pair_sub_left, h1, hσζ, mul_inv_cancel₀ (W.pair_ne_zero z y)]

end S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1
end P2MW
export P2MW.S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1 (solution)
