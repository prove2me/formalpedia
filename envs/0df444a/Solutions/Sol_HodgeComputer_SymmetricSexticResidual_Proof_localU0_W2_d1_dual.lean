-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_d1_dual
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T11:10:07.333729+00:00
-- url     : https://prove2.me/submissions/bdedac86-7ba3-4b66-9fcf-8ea92376c2f1

import Definitions.Def_HodgeComputerSSR_BranchHelpers

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  PolynomialEncoding.KroneckerCheck QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators LaurentSeries PowerSeries

private lemma localU0_W2_d1_dual_proof :
    let A := 5 * S_K - 9 * Q_K
    let B := T_K - 3
    let d1_1 := (-2384185791015625 / 25942282643925774 : K5) *
      (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-A) ^ 15 / B ^ 8
    ValLead 1 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z)) d1_1 := by
  intro A B d1_1
  let w0 := -(k5Params.Bv0 * k5Params.Av0_inv)
  have hB : B ≠ 0 := T_K_sub_3_ne
  have hS : S_K ≠ 0 := S_K_ne_zero
  have hA : A ≠ 0 := fiveS_sub_9Q_ne
  have hw0_eq : w0 = -(25 / 4 : K5) * S_K * A ^ 2 / B ^ 3 := by
    simp only [w0, CoverParams.Bv0, CoverParams.Av0_inv, CoverParams.inv4, CoverParams.inv243,
      k5Params_inv2, k5Params_inv3, k5Params_invT3, k5Params_S, k5Params_Q, A, B]
    field_simp [hB]; ring
  have hw1_eq : -(k5Params.Bv1 * k5Params.Av0_inv) = (243 / 4 : K5) * k5Params.Bv1 / B ^ 3 := by
    simp only [CoverParams.Av0_inv, CoverParams.inv4, k5Params_inv2, k5Params_invT3, B]
    field_simp [hB]; ring
  -- Build `ValDual 0` for all `d2_2..0, d3_3..0` in `Dual K5`, then evaluate `remDeg3_d1/d0`!
  set caD : Dual K5 := ⟨k5Params.ca_h.coeff 0, k5Params.ca_h.coeff 1⟩
  set cbD : Dual K5 := ⟨k5Params.cb_h.coeff 0, k5Params.cb_h.coeff 1⟩
  set q20D : Dual K5 := ⟨k5Params.q20.coeff 0, k5Params.q20.coeff 1⟩
  set q11D : Dual K5 := ⟨k5Params.q11.coeff 0, k5Params.q11.coeff 1⟩
  set q02D : Dual K5 := ⟨k5Params.q02.coeff 0, k5Params.q02.coeff 1⟩
  set c30D : Dual K5 := ⟨k5Params.c30.coeff 0, k5Params.c30.coeff 1⟩
  set c21D : Dual K5 := ⟨k5Params.c21.coeff 0, k5Params.c21.coeff 1⟩
  set c12D : Dual K5 := ⟨k5Params.c12.coeff 0, k5Params.c12.coeff 1⟩
  set c03D : Dual K5 := ⟨k5Params.c03.coeff 0, k5Params.c03.coeff 1⟩
  set WD : Dual K5 := ⟨w0, -(k5Params.Bv1 * k5Params.Av0_inv)⟩
  set c0WD : Dual K5 := Dual.C k5Params.c0_V2 * WD ^ 2 + Dual.C k5Params.c0_V1 * ⟨0, 1⟩ * WD
  set k2WD : Dual K5 := Dual.C k5Params.k2_V2 * WD ^ 2 + Dual.C k5Params.k2_V1 * ⟨0, 1⟩ * WD
  set k3WD : Dual K5 := Dual.C k5Params.k3_V2 * WD ^ 2 + Dual.C k5Params.k3_V1 * ⟨0, 1⟩ * WD
  have hca : ValDual 0 (evalT k5Params.ca_h) caD := ValDual.of_evalT _
  have hcb : ValDual 0 (evalT k5Params.cb_h) cbD := ValDual.of_evalT _
  have hq20 : ValDual 0 (evalT k5Params.q20) q20D := ValDual.of_evalT _
  have hq11 : ValDual 0 (evalT k5Params.q11) q11D := ValDual.of_evalT _
  have hq02 : ValDual 0 (evalT k5Params.q02) q02D := ValDual.of_evalT _
  have hc30 : ValDual 0 (evalT k5Params.c30) c30D := ValDual.of_evalT _
  have hc21 : ValDual 0 (evalT k5Params.c21) c21D := ValDual.of_evalT _
  have hc12 : ValDual 0 (evalT k5Params.c12) c12D := ValDual.of_evalT _
  have hc03 : ValDual 0 (evalT k5Params.c03) c03D := ValDual.of_evalT _
  have hc0W : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.c0W)) c0WD :=
    evalT_toUW_valDual_W2 _ _ _
  have hk2W : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k2W)) k2WD :=
    evalT_toUW_valDual_W2 _ _ _
  have hk3W : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k3W)) k3WD :=
    evalT_toUW_valDual_W2 _ _ _
  set D22 : Dual K5 := q20D * cbD ^ 2 - q11D * caD * cbD + q02D * caD ^ 2
  set D21 : Dual K5 := (-q11D * cbD + 2 * q02D * caD) * c0WD
  set D20 : Dual K5 := q02D * c0WD ^ 2 + cbD ^ 2 * (WD * k2WD)
  set D33 : Dual K5 := c30D * cbD ^ 3 - c21D * caD * cbD ^ 2 + c12D * caD ^ 2 * cbD - c03D * caD ^ 3
  set D32 : Dual K5 := (-c21D * cbD ^ 2 + 2 * c12D * caD * cbD - 3 * c03D * caD ^ 2) * c0WD
  set D31 : Dual K5 := (c12D * cbD - 3 * c03D * caD) * c0WD ^ 2
  set D30 : Dual K5 := -c03D * c0WD ^ 3 + cbD ^ 3 * (WD ^ 2 * k3WD)
  have hmul0 {f g : LaurentSeries K5} {a b : Dual K5} (hf : ValDual 0 f a) (hg : ValDual 0 g b) :
      ValDual 0 (f * g) (a * b) := by simpa only [zero_add] using hf.mul hg
  have hpow0 {f : LaurentSeries K5} {a : Dual K5} (hf : ValDual 0 f a) (m : ℕ) :
      ValDual 0 (f ^ m) (a ^ m) := by simpa only [mul_zero] using hf.pow m
  have hD22 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_2)) D22 := by
    simp only [CoverParams.d2_2, CoverParams.Q5_z, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar,
      map_add, map_sub, map_mul, map_pow]
    exact ((hmul0 hq20 (hpow0 hcb 2)).sub (hmul0 (hmul0 hq11 hca) hcb)).add (hmul0 hq02 (hpow0 hca 2))
  have hD21 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_1)) D21 := by
    simp only [CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul, map_add, map_neg, map_mul, map_ofNat]
    exact hmul0 ((hmul0 hq11.neg hcb).add (hmul0 (hmul0 (ValDual.of_nat 2) hq02) hca)) hc0W
  have hD20 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_0)) D20 := by
    simp only [CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq,
      PairAlg.evalAt_W, map_pow]
    exact (hmul0 hq02 (hmul0 hc0W hc0W |>.eq_d (by ring))).add (hmul0 (hpow0 hcb 2) (hmul0 W2_0_valDual hk2W))
  have hD33 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_3)) D33 := by
    simp only [CoverParams.d3_3, CoverParams.Q7_z, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar,
      map_add, map_sub, map_mul, map_pow]
    exact (((hmul0 hc30 (hpow0 hcb 3)).sub (hmul0 (hmul0 hc21 hca) (hpow0 hcb 2))).add
      (hmul0 (hmul0 hc12 (hpow0 hca 2)) hcb)).sub (hmul0 hc03 (hpow0 hca 3))
  have hD32 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_2)) D32 := by
    simp only [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul, map_add, map_sub,
      map_neg, map_mul, map_pow, map_ofNat]
    exact hmul0 (((hmul0 hc21.neg (hpow0 hcb 2)).add
      (hmul0 (hmul0 (hmul0 (ValDual.of_nat 2) hc12) hca) hcb)).sub
      (hmul0 (hmul0 (ValDual.of_nat 3) hc03) (hpow0 hca 2))) hc0W
  have hD31 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_1)) D31 := by
    simp only [CoverParams.d3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, map_sub, map_mul, map_ofNat]
    exact hmul0 ((hmul0 hc12 hcb).sub (hmul0 (hmul0 (ValDual.of_nat 3) hc03) hca))
      (hmul0 hc0W hc0W |>.eq_d (by ring))
  have hD30 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_0)) D30 := by
    simp only [CoverParams.d3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq,
      PairAlg.evalAt_W, map_neg, map_pow]
    exact (hmul0 hc03.neg (hmul0 hc0W (hmul0 hc0W hc0W) |>.eq_d (by ring))).add
      (hmul0 (hpow0 hcb 3) (hmul0 (hmul0 W2_0_valDual W2_0_valDual |>.eq_d (by ring)) hk3W))
  have hd1_D : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z))
      (remDeg3_d1 D22 D21 D20 D33 D32 D31) := by
    simp only [CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, remDeg3_d1]
    exact (hmul0 hD22 ((hmul0 hD22 hD31).sub (hmul0 hD20 hD33))).sub
      (hmul0 hD21 ((hmul0 hD22 hD32).sub (hmul0 hD21 hD33)))
  have hd0_D : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d0_z))
      (remDeg3_d0 D22 D21 D20 D33 D32 D30) := by
    simp only [CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, remDeg3_d0]
    exact (hmul0 hD22 (hmul0 hD22 hD30)).sub (hmul0 hD20 ((hmul0 hD22 hD32).sub (hmul0 hD21 hD33)))
  -- Compute explicit `(S_K, Q_K, T_K)` values of `D22..D30` using `A = 5*S_K - 9*Q_K, B = T_K - 3`!
  have hca0 : k5Params.ca_h.coeff 0 = -(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K) := by
    simp only [CoverParams.ca_h, quadU_coeff_zero, CoverParams.inv81, CoverParams.inv27,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hca1 : k5Params.ca_h.coeff 1 = (143 / 81 : K5) * S_K ^ 2 - (184 / 27) * S_K * Q_K + (52 / 9) * Q_K ^ 2 := by
    simp only [CoverParams.ca_h, quadU_coeff_one, CoverParams.inv81, CoverParams.inv27, CoverParams.inv9,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hcb0 : k5Params.cb_h.coeff 0 = (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) := by
    simp only [CoverParams.cb_h, quadU_coeff_zero, CoverParams.inv27, CoverParams.inv9,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hcb1 : k5Params.cb_h.coeff 1 = -(92 / 27 : K5) * S_K ^ 2 + (104 / 9) * S_K * Q_K -
      (22 / 3) * Q_K ^ 2 + (10 / 7) * Q_K + 10 / 7 := by
    simp only [CoverParams.cb_h, quadU_coeff_one, CoverParams.inv27, CoverParams.inv9,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q]; ring
  have hq20_0 : k5Params.q20.coeff 0 = -(625 / 81 : K5) * S_K + (250 / 27) * Q_K := by
    simp only [CoverParams.q20, quadU_coeff_zero, CoverParams.inv81, CoverParams.inv27,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hq20_1 : k5Params.q20.coeff 1 = (143 / 81 : K5) * S_K - (92 / 27) * Q_K := by
    simp only [CoverParams.q20, quadU_coeff_one, CoverParams.inv81, CoverParams.inv27,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hq11_0 : k5Params.q11.coeff 0 = (500 / 27 : K5) * S_K - (50 / 3) * Q_K := by
    simp only [CoverParams.q11, quadU_coeff_zero, CoverParams.inv27, k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hq11_1 : k5Params.q11.coeff 1 = -(184 / 27 : K5) * S_K + (104 / 9) * Q_K := by
    simp only [CoverParams.q11, quadU_coeff_one, CoverParams.inv27, CoverParams.inv9,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hq02_0 : k5Params.q02.coeff 0 = -(25 / 3 : K5) * S_K := by
    simp only [CoverParams.q02, quadU_coeff_zero, k5Params_inv3, k5Params_S]; ring
  have hq02_1 : k5Params.q02.coeff 1 = (52 / 9 : K5) * S_K - (22 / 3) * Q_K + 5 / 7 := by
    simp only [CoverParams.q02, quadU_coeff_one, CoverParams.inv9, k5Params_inv3, k5Params_inv7,
      k5Params_S, k5Params_Q]; ring
  have hc30_0 : k5Params.c30.coeff 0 = -(625 / 243 : K5) := by
    simp only [CoverParams.c30, quadU_coeff_zero, CoverParams.inv243, k5Params_inv3]; ring
  have hc30_1 : k5Params.c30.coeff 1 = (143 / 243 : K5) := by
    simp only [CoverParams.c30, quadU_coeff_one, CoverParams.inv243, k5Params_inv3]; ring
  have hc21_0 : k5Params.c21.coeff 0 = (250 / 27 : K5) := by
    simp only [CoverParams.c21, quadU_coeff_zero, CoverParams.inv27, k5Params_inv3]; ring
  have hc21_1 : k5Params.c21.coeff 1 = -(92 / 27 : K5) := by
    simp only [CoverParams.c21, quadU_coeff_one, CoverParams.inv27, k5Params_inv3]; ring
  have hc12_0 : k5Params.c12.coeff 0 = -(25 / 3 : K5) := by
    simp only [CoverParams.c12, quadU_coeff_zero, k5Params_inv3]; ring
  have hc12_1 : k5Params.c12.coeff 1 = (52 / 9 : K5) := by
    simp only [CoverParams.c12, quadU_coeff_one, CoverParams.inv9, k5Params_inv3]; ring
  have hc03_0 : k5Params.c03.coeff 0 = 0 := by
    simp only [CoverParams.c03, quadU_coeff_zero]
  have hc03_1 : k5Params.c03.coeff 1 = -(22 / 9 : K5) := by
    simp only [CoverParams.c03, quadU_coeff_one, CoverParams.inv9, k5Params_inv3]; ring
  -- Factor `iB = B⁻¹` cleanly out of `c0WD`, `WD * k2WD`, `WD^2 * k3WD` so `remDeg3_d1/d0` are division-free `ring`!
  set iB : K5 := B⁻¹
  have hiB : B * iB = 1 := mul_inv_cancel₀ hB
  set w0n : K5 := -(25 / 4 : K5) * S_K * A ^ 2
  set w1n : K5 := (243 / 4 : K5) * k5Params.Bv1
  have hw0_iB : w0 = w0n * iB ^ 3 := by rw [hw0_eq, div_eq_mul_inv, inv_pow]
  have hw1_iB : -(k5Params.Bv1 * k5Params.Av0_inv) = w1n * iB ^ 3 := by
    rw [hw1_eq, div_eq_mul_inv, inv_pow]
  set c0W_s : Dual K5 := ⟨-(4 / 81 : K5) * w0n ^ 2, -(4 / 81 : K5) * (2 * w0n * w1n) + k5Params.c0_V1 * w0n * B⟩
  set Wk2_s : Dual K5 := ⟨-(4 / 81 : K5) * w0n ^ 3, -(4 / 81 : K5) * (3 * w0n ^ 2 * w1n) + k5Params.k2_V1 * w0n ^ 2 * B ^ 2⟩
  set W2k3_s : Dual K5 := ⟨-(4 / 243 : K5) * w0n ^ 4, -(4 / 243 : K5) * (4 * w0n ^ 3 * w1n) + k5Params.k3_V1 * w0n ^ 3 * B ^ 3⟩
  have hc0WD_eq : c0WD = Dual.C (iB ^ 4) * c0W_s := by
    have hc0V2 : k5Params.c0_V2 = -(4 / 81 : K5) * B ^ 2 := by
      simp only [CoverParams.c0_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, B]; ring
    ext
    · simp only [c0WD, c0W_s, WD, Dual.add_val, Dual.mul_val, Dual.pow_eq, Dual.C_val, hw0_iB, hc0V2]
      calc -(4 / 81 : K5) * B ^ 2 * (w0n * iB ^ 3) ^ 2 + k5Params.c0_V1 * 0 * (w0n * iB ^ 3) =
            -(4 / 81 : K5) * w0n ^ 2 * (B * iB) ^ 2 * iB ^ 4 := by ring
        _ = iB ^ 4 * (-(4 / 81 : K5) * w0n ^ 2) := by rw [hiB]; ring
    · simp only [c0WD, c0W_s, WD, Dual.add_eps, Dual.mul_eps, Dual.mul_val, Dual.pow_eq,
        Dual.C_val, Dual.C_eps, Nat.cast_ofNat, Nat.reduceSub, pow_one, hw0_iB, hw1_iB, hc0V2]
      calc -(4 / 81 : K5) * B ^ 2 * (2 * (w0n * iB ^ 3) * (w1n * iB ^ 3)) + 0 * (w0n * iB ^ 3) ^ 2 +
            (k5Params.c0_V1 * 0 * (w1n * iB ^ 3) + (k5Params.c0_V1 * 1 + 0 * 0) * (w0n * iB ^ 3)) =
            -(4 / 81 : K5) * (2 * w0n * w1n) * (B * iB) ^ 2 * iB ^ 4 +
              k5Params.c0_V1 * w0n * iB ^ 3 := by ring
        _ = -(4 / 81 : K5) * (2 * w0n * w1n) * iB ^ 4 + k5Params.c0_V1 * w0n * (B * iB) * iB ^ 3 := by
            rw [hiB]; ring
        _ = iB ^ 4 * (-(4 / 81 : K5) * (2 * w0n * w1n) + k5Params.c0_V1 * w0n * B) + 0 * (-(4 / 81 : K5) * w0n ^ 2) := by
            ring
  have hWk2_eq : WD * k2WD = Dual.C (iB ^ 8) * Wk2_s := by
    have hk2V2 : k5Params.k2_V2 = -(4 / 81 : K5) * B := by
      simp only [CoverParams.k2_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, B]; ring
    ext
    · simp only [k2WD, Wk2_s, WD, Dual.add_val, Dual.mul_val, Dual.pow_eq, Dual.C_val, hw0_iB, hk2V2]
      calc w0n * iB ^ 3 * (-(4 / 81 : K5) * B * (w0n * iB ^ 3) ^ 2 + k5Params.k2_V1 * 0 * (w0n * iB ^ 3)) =
            -(4 / 81 : K5) * w0n ^ 3 * (B * iB) * iB ^ 8 := by ring
        _ = iB ^ 8 * (-(4 / 81 : K5) * w0n ^ 3) := by rw [hiB]; ring
    · simp only [k2WD, Wk2_s, WD, Dual.add_val, Dual.add_eps, Dual.mul_eps, Dual.mul_val,
        Dual.pow_eq, Dual.C_val, Dual.C_eps, Nat.cast_ofNat, Nat.reduceSub, pow_one, hw0_iB, hw1_iB, hk2V2]
      calc w0n * iB ^ 3 * (-(4 / 81 : K5) * B * (2 * (w0n * iB ^ 3) * (w1n * iB ^ 3)) + 0 * (w0n * iB ^ 3) ^ 2 +
              (k5Params.k2_V1 * 0 * (w1n * iB ^ 3) + (k5Params.k2_V1 * 1 + 0 * 0) * (w0n * iB ^ 3))) +
            w1n * iB ^ 3 * (-(4 / 81 : K5) * B * (w0n * iB ^ 3) ^ 2 + k5Params.k2_V1 * 0 * (w0n * iB ^ 3)) =
            -(4 / 81 : K5) * (3 * w0n ^ 2 * w1n) * (B * iB) * iB ^ 8 +
              k5Params.k2_V1 * w0n ^ 2 * iB ^ 6 := by ring
        _ = -(4 / 81 : K5) * (3 * w0n ^ 2 * w1n) * iB ^ 8 + k5Params.k2_V1 * w0n ^ 2 * (B * iB) ^ 2 * iB ^ 6 := by
            rw [hiB]; ring
        _ = iB ^ 8 * (-(4 / 81 : K5) * (3 * w0n ^ 2 * w1n) + k5Params.k2_V1 * w0n ^ 2 * B ^ 2) +
              0 * (-(4 / 81 : K5) * w0n ^ 3) := by
            ring
  have hW2k3_eq : WD ^ 2 * k3WD = Dual.C (iB ^ 12) * W2k3_s := by
    have hk3V2 : k5Params.k3_V2 = -(4 / 243 : K5) := by
      simp only [CoverParams.k3_V2, CoverParams.inv243, k5Params_inv3]; ring
    ext
    · simp only [k3WD, W2k3_s, WD, Dual.add_val, Dual.mul_val, Dual.pow_eq, Dual.C_val, hw0_iB, hk3V2]; ring
    · simp only [k3WD, W2k3_s, WD, Dual.add_val, Dual.add_eps, Dual.mul_eps, Dual.mul_val,
        Dual.pow_eq, Dual.C_val, Dual.C_eps, Nat.cast_ofNat, Nat.reduceSub, pow_one, hw0_iB, hw1_iB, hk3V2]
      calc (w0n * iB ^ 3) ^ 2 * (-(4 / 243 : K5) * (2 * (w0n * iB ^ 3) * (w1n * iB ^ 3)) + 0 * (w0n * iB ^ 3) ^ 2 +
              (k5Params.k3_V1 * 0 * (w1n * iB ^ 3) + (k5Params.k3_V1 * 1 + 0 * 0) * (w0n * iB ^ 3))) +
            2 * (w0n * iB ^ 3) * (w1n * iB ^ 3) * (-(4 / 243 : K5) * (w0n * iB ^ 3) ^ 2 + k5Params.k3_V1 * 0 * (w0n * iB ^ 3)) =
            -(4 / 243 : K5) * (4 * w0n ^ 3 * w1n) * iB ^ 12 + k5Params.k3_V1 * w0n ^ 3 * (B * iB) ^ 3 * iB ^ 9 := by
            rw [hiB]; ring
        _ = iB ^ 12 * (-(4 / 243 : K5) * (4 * w0n ^ 3 * w1n) + k5Params.k3_V1 * w0n ^ 3 * B ^ 3) +
              0 * (-(4 / 243 : K5) * w0n ^ 4) := by ring
  set D21_s : Dual K5 := (-q11D * cbD + 2 * q02D * caD) * c0W_s
  set D20_s : Dual K5 := q02D * c0W_s ^ 2 + cbD ^ 2 * Wk2_s
  set D32_s : Dual K5 := (-c21D * cbD ^ 2 + 2 * c12D * caD * cbD - 3 * c03D * caD ^ 2) * c0W_s
  set D31_s : Dual K5 := (c12D * cbD - 3 * c03D * caD) * c0W_s ^ 2
  set D30_s : Dual K5 := -c03D * c0W_s ^ 3 + cbD ^ 3 * W2k3_s
  have hD21_sc : D21 = Dual.C (iB ^ 4) * D21_s := by dsimp only [D21, D21_s]; rw [hc0WD_eq]; ring
  have hD20_sc : D20 = Dual.C (iB ^ 8) * D20_s := by
    have hpow : Dual.C (iB ^ 4) ^ 2 = Dual.C (iB ^ 8) := by
      ext <;> simp only [Dual.pow_eq, Dual.C_val, Dual.C_eps] <;> ring
    change q02D * c0WD ^ 2 + cbD ^ 2 * (WD * k2WD) = Dual.C (iB ^ 8) * (q02D * c0W_s ^ 2 + cbD ^ 2 * Wk2_s)
    rw [hc0WD_eq, hWk2_eq, mul_pow, hpow]; ring
  have hD32_sc : D32 = Dual.C (iB ^ 4) * D32_s := by dsimp only [D32, D32_s]; rw [hc0WD_eq]; ring
  have hD31_sc : D31 = Dual.C (iB ^ 8) * D31_s := by
    have hpow : Dual.C (iB ^ 4) ^ 2 = Dual.C (iB ^ 8) := by
      ext <;> simp only [Dual.pow_eq, Dual.C_val, Dual.C_eps] <;> ring
    change (c12D * cbD - 3 * c03D * caD) * c0WD ^ 2 = Dual.C (iB ^ 8) * ((c12D * cbD - 3 * c03D * caD) * c0W_s ^ 2)
    rw [hc0WD_eq, mul_pow, hpow]; ring
  have hD30_sc : D30 = Dual.C (iB ^ 12) * D30_s := by
    have hpow : Dual.C (iB ^ 4) ^ 3 = Dual.C (iB ^ 12) := by
      ext <;> simp only [Dual.pow_eq, Dual.C_val, Dual.C_eps] <;> ring
    change -c03D * c0WD ^ 3 + cbD ^ 3 * (WD ^ 2 * k3WD) = Dual.C (iB ^ 12) * (-c03D * c0W_s ^ 3 + cbD ^ 3 * W2k3_s)
    rw [hc0WD_eq, hW2k3_eq, mul_pow, hpow]; ring
  -- Flatten `D22..D30_s` into plain `K5` values first so `remDeg3_d1/d0` close in <0.1s!
  have h2v : (2 : Dual K5).val = 2 := by rw [← one_add_one_eq_two, Dual.add_val]; exact one_add_one_eq_two
  have h2e : (2 : Dual K5).eps = 0 := by rw [← one_add_one_eq_two, Dual.add_eps]; exact add_zero 0
  have h3v : (3 : Dual K5).val = 3 := by
    rw [show (3 : Dual K5) = 2 + 1 by ring, Dual.add_val, h2v, show (1 : Dual K5).val = 1 from rfl]; ring
  have h3e : (3 : Dual K5).eps = 0 := by rw [show (3 : Dual K5) = 2 + 1 by ring, Dual.add_eps, h2e]; exact add_zero 0
  have hD22_v : D22.val = (15625 / 59049 : K5) * S_K * A ^ 4 := by
    simp only [D22, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      q20D, q11D, q02D, caD, cbD, hq20_0, hq11_0, hq02_0, hca0, hcb0, A]; ring
  have hD21_v : D21_s.val = (15625 / 59049 : K5) * S_K * A ^ 4 * (-2 * w0n * S_K) := by
    simp only [D21_s, c0W_s, Dual.add_val, Dual.mul_val, Dual.neg_val, h2v,
      q11D, q02D, caD, cbD, hq11_0, hq02_0, hca0, hcb0, w0n, A]; ring
  have hD20_v : D20_s.val = (15625 / 59049 : K5) * S_K * A ^ 4 * (w0n * S_K) ^ 2 := by
    simp only [D20_s, c0W_s, Wk2_s, Dual.add_val, Dual.mul_val, Dual.pow_eq,
      q02D, cbD, hq02_0, hcb0, w0n, A]; ring
  have hD33_v : D33.val = -(781250 / 4782969 : K5) * S_K * A ^ 5 := by
    simp only [D33, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      c30D, c21D, c12D, c03D, caD, cbD, hc30_0, hc21_0, hc12_0, hc03_0, hca0, hcb0, A]; ring
  have hD32_v : D32_s.val = -(781250 / 4782969 : K5) * S_K * A ^ 5 * (-6 * w0n * S_K) := by
    simp only [D32_s, c0W_s, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.neg_val, Dual.pow_eq, h2v, h3v,
      c21D, c12D, c03D, caD, cbD, hc21_0, hc12_0, hc03_0, hca0, hcb0, w0n, A]; ring
  have hD31_v : D31_s.val = -(781250 / 4782969 : K5) * S_K * A ^ 5 * (9 * (w0n * S_K) ^ 2) := by
    simp only [D31_s, c0W_s, Dual.sub_val, Dual.mul_val, Dual.pow_eq, h3v,
      c12D, c03D, caD, cbD, hc12_0, hc03_0, hca0, hcb0, w0n, A]; ring
  have hD30_v : D30_s.val = -(781250 / 4782969 : K5) * S_K * A ^ 5 * (-4 * (w0n * S_K) ^ 3) := by
    simp only [D30_s, c0W_s, W2k3_s, Dual.add_val, Dual.mul_val, Dual.neg_val, Dual.pow_eq,
      c03D, cbD, hc03_0, hcb0, w0n, A]; ring
  set d22e := D22.eps; set d21e := D21_s.eps; set d20e := D20_s.eps
  set d33e := D33.eps; set d32e := D32_s.eps; set d31e := D31_s.eps; set d30e := D30_s.eps
  have hd1_eps_id :
      (remDeg3_d1 D22 D21_s D20_s D33 D32_s D31_s).eps =
        D22.val ^ 2 * d31e + (2 * D22.val * D31_s.val - D20_s.val * D33.val - D21_s.val * D32_s.val) * d22e +
        (2 * D21_s.val * D33.val - D22.val * D32_s.val) * d21e - D22.val * D33.val * d20e +
        (D21_s.val ^ 2 - D22.val * D20_s.val) * d33e - D21_s.val * D22.val * d32e := by
    simp only [remDeg3_d1, Dual.sub_eps, Dual.mul_eps, Dual.sub_val, Dual.mul_val,
      d22e, d21e, d20e, d33e, d32e, d31e]; ring
  have hd0_eps_id :
      (remDeg3_d0 D22 D21_s D20_s D33 D32_s D30_s).eps =
        D22.val ^ 2 * d30e + (2 * D22.val * D30_s.val - D20_s.val * D32_s.val) * d22e +
        D20_s.val * D33.val * d21e + (D21_s.val * D33.val - D22.val * D32_s.val) * d20e +
        D20_s.val * D21_s.val * d33e - D20_s.val * D22.val * d32e := by
    simp only [remDeg3_d0, Dual.sub_eps, Dual.mul_eps, Dual.sub_val, Dual.mul_val,
      d22e, d21e, d20e, d33e, d32e, d30e]; ring
  -- Notice the miracle: `D2_v(z) = D22_v*(z - r)^2`, `D3_v(z) = D33_v*(z - r)^2*(z - 4r)`!
  have hd1_eps_simp :
      (remDeg3_d1 D22 D21_s D20_s D33 D32_s D31_s).eps =
        ((15625 / 59049 : K5) * S_K * A ^ 4) ^ 2 *
          (d31e + 2 * (w0n * S_K) * d32e + 3 * (w0n * S_K) ^ 2 * d33e) -
        ((15625 / 59049 : K5) * S_K * A ^ 4) * (-(781250 / 4782969 : K5) * S_K * A ^ 5) *
          (d20e - 2 * (w0n * S_K) * d21e - 5 * (w0n * S_K) ^ 2 * d22e) := by
    rw [hd1_eps_id, hD22_v, hD21_v, hD20_v, hD33_v, hD32_v, hD31_v]; ring
  have hd0_eps_simp :
      (remDeg3_d0 D22 D21_s D20_s D33 D32_s D30_s).eps =
        ((15625 / 59049 : K5) * S_K * A ^ 4) ^ 2 *
          (d30e - (w0n * S_K) ^ 2 * d32e - 2 * (w0n * S_K) ^ 3 * d33e) +
        ((15625 / 59049 : K5) * S_K * A ^ 4) * (-(781250 / 4782969 : K5) * S_K * A ^ 5) * (w0n * S_K) *
          (4 * d20e + (w0n * S_K) * d21e - 2 * (w0n * S_K) ^ 2 * d22e) := by
    rw [hd0_eps_id, hD22_v, hD21_v, hD20_v, hD33_v, hD32_v, hD30_v]; ring
  have hrem_d1 : remDeg3_d1 D22 D21 D20 D33 D32 D31 = ⟨0, d1_1⟩ := by
    have hsc : remDeg3_d1 D22 D21 D20 D33 D32 D31 = Dual.C (iB ^ 8) * remDeg3_d1 D22 D21_s D20_s D33 D32_s D31_s := by
      simp only [remDeg3_d1, hD21_sc, hD20_sc, hD32_sc, hD31_sc]
      have hpow : Dual.C (iB ^ 4) * Dual.C (iB ^ 4) = Dual.C (iB ^ 8) := by
        ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps] <;> ring
      calc D22 * (D22 * (Dual.C (iB ^ 8) * D31_s) - Dual.C (iB ^ 8) * D20_s * D33) -
            Dual.C (iB ^ 4) * D21_s * (D22 * (Dual.C (iB ^ 4) * D32_s) - Dual.C (iB ^ 4) * D21_s * D33) =
          Dual.C (iB ^ 8) * (D22 * (D22 * D31_s - D20_s * D33)) -
            (Dual.C (iB ^ 4) * Dual.C (iB ^ 4)) * (D21_s * (D22 * D32_s - D21_s * D33)) := by ring
        _ = Dual.C (iB ^ 8) * (D22 * (D22 * D31_s - D20_s * D33) - D21_s * (D22 * D32_s - D21_s * D33)) := by
          rw [hpow]; ring
    have hpoly : remDeg3_d1 D22 D21_s D20_s D33 D32_s D31_s =
        ⟨0, (-2384185791015625 / 25942282643925774 : K5) *
          (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-A) ^ 15⟩ := by
      ext
      · simp only [remDeg3_d1, Dual.sub_val, Dual.mul_val, hD22_v, hD21_v, hD20_v, hD33_v, hD32_v, hD31_v]; ring
      · rw [hd1_eps_simp]
        simp only [d22e, d21e, d20e, d33e, d32e, d31e, D22, D21_s, D20_s, D33, D32_s, D31_s, c0W_s, Wk2_s,
          Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.neg_val, Dual.pow_eq,
          Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.neg_eps, h2v, h2e, h3v, h3e,
          Nat.cast_ofNat, Nat.reduceSub, pow_one,
          q20D, q11D, q02D, c30D, c21D, c12D, c03D, caD, cbD,
          hq20_0, hq20_1, hq11_0, hq11_1, hq02_0, hq02_1,
          hc30_0, hc30_1, hc21_0, hc21_1, hc12_0, hc12_1, hc03_0, hc03_1,
          hca0, hca1, hcb0, hcb1, w0n, w1n,
          CoverParams.Bv1, CoverParams.c0_V1, CoverParams.k2_V1,
          CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, CoverParams.inv243,
          k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T, A, B]
        ring
    rw [hsc, hpoly]
    ext <;> simp [d1_1, iB, div_eq_mul_inv, inv_pow]; ring
  rw [hrem_d1] at hd1_D
  exact ⟨hd1_D.val.inc hd1_D.c0, hd1_D.c1⟩

end SymmetricSexticResidual.LocalResidueU0

theorem solution :
    let A := 5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K
    let B := SymmetricSexticResidual.K5Field.T_K - 3
    let d1_1 := (-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
      (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K +
        77 * SymmetricSexticResidual.K5Field.T_K - 210) *
      SymmetricSexticResidual.K5Field.S_K ^ 6 * (-A) ^ 15 / B ^ 8
    QuadraticCovers.ValLead 1
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.d1_z)) d1_1 :=
  SymmetricSexticResidual.LocalResidueU0.localU0_W2_d1_dual_proof
