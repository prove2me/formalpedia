-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.residue_zero_eta
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T15:08:33.398801+00:00
-- url     : https://prove2.me/submissions/fe8f6051-83e6-43c7-b315-e0afed5a8d78

import Definitions.Def_HodgeComputerSSR_BranchHelpers
import Definitions.Def_HodgeComputerSSR_RUData
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_reg_identities
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_W2_d1_dual
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_W2_d0_dual
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_W2_res_dual
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br1_vanishes
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br2_g_lead
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br2_A0U_Z2
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br2_q1_cancel

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueData
  QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators LaurentSeries PowerSeries

private abbrev numM_isPolyDeg3 := @HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.numM_deg3
private abbrev W2_0_d1_d0_res :=
  And.intro HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_d1_dual
    (And.intro HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_d0_dual.1
      HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_res_dual.1)
private abbrev numM_12_of_eq_interp := HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_g_lead.1
private abbrev br2_0_g_lead := @HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_g_lead.2
private abbrev br2_0_A0U_Z2_eval := HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_A0U_Z2

lemma br2_0_eta_AC_coeff_neg_one : (br2_0 eta_AC).coeff (-1) = toK5_RU := by
  let U := HahnSeries.single (1 : ℤ) (1 : K5)
  let V := W2_0 / U
  let ca := evalT k5Params.ca_h
  let cb := evalT k5Params.cb_h
  let c0W := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.c0W)
  let d2_2 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_2)
  let d2_1 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_1)
  let d2_0 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_0)
  let d1 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z)
  let d0 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d0_z)
  let res := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)
  let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K)
      (z / W2_0) (-(ca * z + c0W) / (W2_0 * cb)) U V
  let p := interp4 g
  let P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
  let P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
  have hbr : br2_0 eta_AC =
      (-(P1 * d0 - P0 * d1) * U ^ 3 * W2_0 * cb ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W2_0 + evalT k5Params.bW) * evalT k5Params.Q5_z ^ 3 * res) :=
    branchHom_eta_AC_of_eq ψ0 ψ0_C W2_0 W2_0_eq_ψ0 U ψ0_X evalT (RingHom.ext ψ0_toRat)
      V ca cb c0W d2_2 d2_1 d2_0 d1 d0 res g p P1 P0
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [hbr]
  have hp_def : p = interp4 g := rfl
  have hP1_def : P1 = remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1 := rfl
  have hP0_def : P0 = remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2 := rfl
  clear_value P1 P0 p
  have hS := S_K_ne_zero; have hA := fiveS_sub_9Q_ne; have hB := T_K_sub_3_ne
  set A := 5 * S_K - 9 * Q_K
  set B := T_K - 3
  set w0 : K5 := -(k5Params.Bv0 * k5Params.Av0_inv)
  have hw0_eq : w0 = -(25 / 4 : K5) * S_K * A ^ 2 / B ^ 3 := by
    simp only [w0, CoverParams.Bv0, CoverParams.Av0_inv, CoverParams.inv4, CoverParams.inv243,
      k5Params_inv2, k5Params_inv3, k5Params_invT3, k5Params_S, k5Params_Q, A, B]
    field_simp [hB]; ring
  have hw0_ne : w0 ≠ 0 := by
    rw [hw0_eq]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero
      (by exact_mod_cast (by decide : (25 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (4 : ℕ) ≠ 0)))) hS) (pow_ne_zero 2 hA)) (pow_ne_zero 3 hB)
  have hw0_L : ValLead 0 W2_0 w0 := W2_0_valDual.toValLead
  have hU_L : ValLead 1 U 1 := ValLead.of_single 1 1
  have hV_L : ValLead (-1) V w0 := (hw0_L.div_of_ne hU_L one_ne_zero).eq_k (by omega) |>.eq_c (div_one w0)
  set ca0 : K5 := -(25 / 81 : K5) * A * (5 * S_K - 3 * Q_K)
  set cb0 : K5 := (50 / 27 : K5) * S_K * A
  set c0W0 : K5 := k5Params.c0_V2 * w0 ^ 2
  have hca_L : ValLead 0 ca ca0 := (ValLead.of_evalT _).eq_c (by
    simp only [CoverParams.ca_h, quadU_coeff_zero, CoverParams.inv81, CoverParams.inv27, k5Params_inv3, k5Params_S, k5Params_Q, ca0, A]; ring)
  have hcb_L : ValLead 0 cb cb0 := (ValLead.of_evalT _).eq_c (by
    simp only [CoverParams.cb_h, quadU_coeff_zero, CoverParams.inv27, CoverParams.inv9, k5Params_inv3, k5Params_S, k5Params_Q, cb0, A]; ring)
  have hcb0_ne : cb0 ≠ 0 := mul_ne_zero (mul_ne_zero (div_ne_zero
    (by exact_mod_cast (by decide : (50 : ℕ) ≠ 0))
    (by exact_mod_cast (by decide : (27 : ℕ) ≠ 0))) hS) hA
  have hc0W_L : ValLead 0 c0W c0W0 := (evalT_toUW_valDual_W2 _ _ _).toValLead.eq_c (by
    simp [Dual.C, Dual.pow_eq, c0W0, w0])
  set q2_0 : K5 := (15625 / 59049 : K5) * S_K * A ^ 4
  have hQ5_L : ValLead 0 (evalT k5Params.Q5_z) q2_0 := (ValLead.of_evalT _).eq_c (by
    simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.Q5_z, CoverParams.q20, CoverParams.q11,
      CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, q2_0, A]; ring)
  have hd2_2_L : ValLead 0 d2_2 q2_0 := by
    simpa only [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5_L
  set z2 : K5 := w0 * S_K / B
  have hd2_1_L : ValLead 0 d2_1 (-2 * q2_0 * z2) := by
    simp only [d2_1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hsc : ValLead 0 (evalT (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h))
        (-(1250 / 729 : K5) * S_K * A ^ 2) := (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.q11, CoverParams.q02,
        CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
        CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_neg, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, A]; ring)
    exact (hsc.mul hc0W_L).eq_k (by omega) |>.eq_c (by
      simp only [c0W0, hw0_eq, z2, q2_0, CoverParams.c0_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, A, B]
      field_simp [hB]; ring)
  have hd2_0_L : ValLead 0 d2_0 (q2_0 * z2 ^ 2) := by
    simp only [d2_0, CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, PairAlg.evalAt_W, map_pow]
    have hq02 : ValLead 0 (evalT k5Params.q02) (-(25 / 3 : K5) * S_K) := (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.q02, quadU_coeff_zero, k5Params_inv3, k5Params_S]; ring)
    have hk2W_L : ValLead 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k2W)) (k5Params.k2_V2 * w0 ^ 2) :=
      (evalT_toUW_valDual_W2 _ _ _).toValLead.eq_c (by simp [Dual.C, Dual.pow_eq, w0])
    exact (((hq02.mul (hc0W_L.mul hc0W_L)).eq_k (by omega)).add
      (((hcb_L.pow 2).mul (hw0_L.mul hk2W_L)).eq_k (by omega))).eq_c (by
      simp only [c0W0, cb0, hw0_eq, z2, q2_0, CoverParams.c0_V2, CoverParams.k2_V2,
        CoverParams.inv81, k5Params_inv3, k5Params_T, A, B]
      field_simp [hB]; ring)
  obtain ⟨hd1_L, hd0_L, hcd_eq, hres_L, hcd_ne, hq2_ne⟩ := W2_0_d1_d0_res
  have h2W_L : ValLead 0 (2 * W2_0 + evalT k5Params.bW) w0 := by
    have hbW0 : ValLead 0 (evalT k5Params.bW) (-w0) := (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.bW, CoverParams.Bv, coeff_C_mul, quadU_coeff_zero, w0]; ring)
    exact ((((ValLead.of_nat 2).mul hw0_L).eq_k (by omega)).add hbW0).eq_c (by simp; ring)
  set cd : K5 := (-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-A) ^ 17 / B ^ 12
  set d1_1 : K5 := (-2384185791015625 / 25942282643925774 : K5) *
    (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-A) ^ 15 / B ^ 8
  set d0_1 : K5 := (-59604644775390625 / 103769130575703096 : K5) *
    (225 * S_K - 45 * Q_K + 77 * T_K - 189) * S_K ^ 8 * (-A) ^ 17 / B ^ 12
  -- Denominator `ValLead 2`!
  have hden_L : ValLead 2
      (81 * HahnSeries.C k5Params.Av0 * (2 * W2_0 + evalT k5Params.bW) * evalT k5Params.Q5_z ^ 3 * res)
      (81 * k5Params.Av0 * w0 * q2_0 ^ 3 * (cd ^ 2 / q2_0)) :=
    (((((ValLead.of_nat 81).mul (ValLead.of_C k5Params.Av0)).mul h2W_L).mul (hQ5_L.pow 3)).mul hres_L).eq_k
      (by omega) |>.eq_c (by push_cast; rfl)
  have h81_ne : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  have hden_ne : 81 * k5Params.Av0 * w0 * q2_0 ^ 3 * (cd ^ 2 / q2_0) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h81_ne k5Params_Av0_ne) hw0_ne)
      (pow_ne_zero 3 hq2_ne)) (div_ne_zero (pow_ne_zero 2 hcd_ne) hq2_ne)
  let q1_lead0 : K5 → K5 → K5 := fun a b =>
    let qY0 := 9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a +
      (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b +
      (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))
    let cA0 := 9 * ((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a +
      (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b +
      (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K))
    w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 * qY0 + cA0 * EB_of S_K Q_K T_K x_K y_K 0 1)
  let g0 : K5 → K5 := fun z =>
    let a := z / w0; let b := -(ca0 * z + c0W0) / (w0 * cb0)
    w0 ^ 2 * A0U_12_of (RingHom.id K5) a b * q1_lead0 a b
  have hg_L : ∀ z : K5, ValLead (-3) (g (HahnSeries.C z)) (g0 z) :=
    br2_0_g_lead hw0_eq hw0_ne hcb0_ne rfl rfl rfl hw0_L hU_L hV_L hca_L hcb_L hc0W_L
  -- Transport `ValLead (-3)` across `interp4` and `remDeg4_P1 / remDeg4_P0`!
  obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ : ValLead (-3) p.1 (interp4 g0).1 ∧
      ValLead (-3) p.2.1 (interp4 g0).2.1 ∧ ValLead (-3) p.2.2.1 (interp4 g0).2.2.1 ∧
      ValLead (-3) p.2.2.2.1 (interp4 g0).2.2.2.1 ∧ ValLead (-3) p.2.2.2.2 (interp4 g0).2.2.2.2 :=
    hp_def.symm ▸ ValLead.interp4_of hg_L
  set q := interp4 g0
  set P1_0 := remDeg4_P1 q2_0 (-2 * q2_0 * z2) (q2_0 * z2 ^ 2) q.1 q.2.1 q.2.2.1 q.2.2.2.1
  set P0_0 := remDeg4_P0 q2_0 (-2 * q2_0 * z2) (q2_0 * z2 ^ 2) q.1 q.2.1 q.2.2.1 q.2.2.2.2
  have hP1_L : ValLead (-3) P1 P1_0 := by
    rw [hP1_def]; simp only [P1_0, remDeg4_P1]
    have hr3 := ((hd2_2_L.mul hp3).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hp4).eq_k (k' := -3) (by omega))
    have hr2 := ((hd2_2_L.mul hp2).eq_k (k' := -3) (by omega)).sub ((hd2_0_L.mul hp4).eq_k (k' := -3) (by omega))
    have hs2 := ((hd2_2_L.mul hr2).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hr3).eq_k (k' := -3) (by omega))
    have hs1 := (((hd2_2_L.pow 2).mul hp1).eq_k (k' := -3) (by omega)).sub ((hd2_0_L.mul hr3).eq_k (k' := -3) (by omega))
    exact ((hd2_2_L.mul hs1).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hs2).eq_k (k' := -3) (by omega))
  have hP0_L : ValLead (-3) P0 P0_0 := by
    rw [hP0_def]; simp only [P0_0, remDeg4_P0]
    have hr3 := ((hd2_2_L.mul hp3).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hp4).eq_k (k' := -3) (by omega))
    have hr2 := ((hd2_2_L.mul hp2).eq_k (k' := -3) (by omega)).sub ((hd2_0_L.mul hp4).eq_k (k' := -3) (by omega))
    have hs2 := ((hd2_2_L.mul hr2).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hr3).eq_k (k' := -3) (by omega))
    exact (((hd2_2_L.pow 3).mul hp0).eq_k (k' := -3) (by omega)).sub ((hd2_0_L.mul hs2).eq_k (k' := -3) (by omega))
  have hnum_L : ValLead 1 (-(P1 * d0 - P0 * d1) * U ^ 3 * W2_0 * cb ^ 4)
      (-(P1_0 * d0_1 - P0_0 * d1_1) * w0 * cb0 ^ 4) := by
    have hcomb := (((hP1_L.mul hd0_L).eq_k (k' := -2) (by omega)).sub ((hP0_L.mul hd1_L).eq_k (k' := -2) (by omega))).neg
    exact (((hcomb.mul (hU_L.pow 3)).mul hw0_L).mul (hcb_L.pow 4)).eq_k (by omega) |>.eq_c (by ring)
  have hquot_L := (hnum_L.div_of_ne hden_L hden_ne).eq_k (k' := -1) (by omega)
  rw [hquot_L.c0]
  clear_value U V ca cb c0W d2_2 d2_1 d2_0 d1 d0 res g
  -- Evaluate `P1_0` and `P0_0` at double root `z2` via `remDeg4_eq` in `Dual K5` at `Z2 = ⟨z2, w0⟩`!
  -- First build explicit polynomials `P_A, P_Q : K5[X]` for `g0 z = w0^2 * A0U_12(a(z), b(z)) * q1_lead0(a(z), b(z))`!
  set aX : K5[X] := C (1 / w0) * X
  set bX : K5[X] := C (-ca0 / (w0 * cb0)) * X + C (-c0W0 / (w0 * cb0))
  have haX_eval (z : K5) : aX.eval z = z / w0 := by simp [aX]; ring
  have hbX_eval (z : K5) : bX.eval z = -(ca0 * z + c0W0) / (w0 * cb0) := by simp [bX]; ring
  set P_A : K5[X] := A0U_12_of Polynomial.C aX bX
  have hPA_eval (z : K5) : P_A.eval z = A0U_12_of (RingHom.id K5) (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0)) := by
    have h := map_A0U_12_of (Polynomial.evalRingHom z) Polynomial.C aX bX
    have hcomp : (Polynomial.evalRingHom z).comp Polynomial.C = RingHom.id K5 :=
      RingHom.ext (fun r => Polynomial.eval_C)
    simpa only [P_A, hcomp, Polynomial.coe_evalRingHom, haX_eval, hbX_eval] using h
  have hPA_deg3 : P_A.natDegree ≤ 3 := by
    have hdeg : IsPolyDeg 3 (fun z => P_A.eval z) := by
      have hmi (mi : Fin 10) : IsPolyDeg 3 (fun z => numM_12_of (RingHom.id K5) mi (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0))) := by
        have h1 (U : K5) : IsPolyDeg 3 (fun z => numM mi (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0))
            (S_K - z / w0 * T_K) (Q_K - -(ca0 * z + c0W0) / (w0 * cb0) * T_K) U 1) :=
          (numM_isPolyDeg3 mi S_K Q_K T_K U 1 (1 / w0) 0 (-ca0 / (w0 * cb0)) (-c0W0 / (w0 * cb0))).congr
            (fun z => by congr 1 <;> ring)
        exact (((((h1 1).sub (h1 (-1))).smul_left 8).sub ((h1 2).sub (h1 (-2)))).div_const 12).congr
          (fun z => (numM_12_of_eq_interp mi _ _).symm)
      have hp (i j : Fin 10) : IsPolyDeg 3 (fun z =>
          5 * numM_12_of (RingHom.id K5) i (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0)) -
          9 * numM_12_of (RingHom.id K5) j (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0))) :=
        ((hmi i).smul_left 5).sub ((hmi j).smul_left 9)
      exact (((((hp 0 1).smul_left (-(19708 / 1257375 : K5))).add
        ((hp 1 2).smul_left (1472 / 1257375 : K5))).sub
        ((hp 3 5).smul_left (16 / 729 : K5))).add
        ((hp 4 6).smul_left (188 / 2025 : K5))).congr (fun z => by rw [hPA_eval]; simp [A0U_12_of])
    rcases hdeg with ⟨Q_poly, hQ_deg, hQ_eval⟩
    have : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
    have hEq : P_A = Q_poly := Polynomial.funext (fun z => hQ_eval z)
    rwa [hEq]
  let q1_c0 : K5 := 9 * w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 *
      (QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) +
    (H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) *
      EB_of S_K Q_K T_K x_K y_K 0 1)
  let q1_c1 : K5 := 9 * w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 *
      (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) +
    (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) *
      EB_of S_K Q_K T_K x_K y_K 0 1)
  let q1_c2 : K5 := 9 * w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 *
      (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2) +
    (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K) *
      EB_of S_K Q_K T_K x_K y_K 0 1)
  set P_Q : K5[X] := C q1_c0 * aX + C q1_c1 * bX + C q1_c2
  have hPQ_eval (z : K5) : P_Q.eval z = q1_lead0 (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0)) := by
    simp only [P_Q, eval_add, eval_mul, eval_C, haX_eval, hbX_eval, q1_c0, q1_c1, q1_c2, q1_lead0]; ring
  have hPQ_deg1 : P_Q.natDegree ≤ 1 := by
    have haX_deg : aX.natDegree ≤ 1 := le_trans (natDegree_C_mul_le _ _) (by simp)
    have hbX_deg : bX.natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (le_trans (natDegree_C_mul_le _ _) (by simp)) (by simp))
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le (le_trans (natDegree_C_mul_le _ _) haX_deg)
        (le_trans (natDegree_C_mul_le _ _) hbX_deg))) (by simp))
  set P_g0 : K5[X] := C (w0 ^ 2) * P_A * P_Q
  have hPg0_deg4 : P_g0.natDegree ≤ 4 :=
    natDegree_mul_le.trans (Nat.add_le_add (le_trans (natDegree_C_mul_le _ _) hPA_deg3) hPQ_deg1)
  have hPg0_eval (z : K5) : g0 z = P_g0.eval z := by
    simp only [g0, P_g0, eval_mul, eval_C, hPA_eval, hPQ_eval]
  have hq_coeffs : q = (P_g0.coeff 4, P_g0.coeff 3, P_g0.coeff 2, P_g0.coeff 1, P_g0.coeff 0) := by
    apply interp4_eq
    intro z
    rw [hPg0_eval z, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hPg0_deg4)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    ring
  -- Evaluate `P_g0` in `Dual K5` at `Z2 = ⟨z2, w0⟩`!
  set Z2 : Dual K5 := ⟨z2, w0⟩
  have hPg0_Z2 : Dual.C q.1 * Z2 ^ 4 + Dual.C q.2.1 * Z2 ^ 3 + Dual.C q.2.2.1 * Z2 ^ 2 +
      Dual.C q.2.2.2.1 * Z2 + Dual.C q.2.2.2.2 = P_g0.eval₂ Dual.C Z2 := by
    rw [hq_coeffs, Polynomial.eval₂_eq_sum_range' Dual.C (Nat.lt_succ_of_le hPg0_deg4)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, mul_one, pow_one]
    ring
  have hrem_Z2 : Dual.C q2_0 ^ 3 * (P_g0.eval₂ Dual.C Z2) = Dual.C P1_0 * Z2 + Dual.C P0_0 := by
    have hrem := remDeg4_eq (Dual.C q2_0) (Dual.C (-2 * q2_0 * z2)) (Dual.C (q2_0 * z2 ^ 2))
      (Dual.C q.1) (Dual.C q.2.1) (Dual.C q.2.2.1) (Dual.C q.2.2.2.1) (Dual.C q.2.2.2.2) Z2
    have hquad0 : Dual.C q2_0 * Z2 ^ 2 + Dual.C (-2 * q2_0 * z2) * Z2 + Dual.C (q2_0 * z2 ^ 2) = 0 := by
      ext <;> simp [Z2, Dual.C_val, Dual.C_eps, Dual.pow_eq] <;> ring
    have hP1_map : remDeg4_P1 (Dual.C q2_0) (Dual.C (-2 * q2_0 * z2)) (Dual.C (q2_0 * z2 ^ 2))
        (Dual.C q.1) (Dual.C q.2.1) (Dual.C q.2.2.1) (Dual.C q.2.2.2.1) = Dual.C P1_0 := by
      simp only [remDeg4_P1, P1_0, map_sub, map_mul, map_pow]
    have hP0_map : remDeg4_P0 (Dual.C q2_0) (Dual.C (-2 * q2_0 * z2)) (Dual.C (q2_0 * z2 ^ 2))
        (Dual.C q.1) (Dual.C q.2.1) (Dual.C q.2.2.1) (Dual.C q.2.2.2.2) = Dual.C P0_0 := by
      simp only [remDeg4_P0, P0_0, map_sub, map_mul, map_pow]
    rw [hPg0_Z2, hquad0, mul_zero, zero_add, hP1_map, hP0_map] at hrem
    exact hrem
  have hP_val : q2_0 ^ 3 * (P_g0.eval₂ Dual.C Z2).val = P1_0 * z2 + P0_0 := by
    have h := congrArg Dual.val hrem_Z2
    simpa [Z2, Dual.C_val, Dual.C_eps, Dual.pow_eq] using h
  have hP_eps : q2_0 ^ 3 * (P_g0.eval₂ Dual.C Z2).eps = P1_0 * w0 := by
    have h := congrArg Dual.eps hrem_Z2
    simpa [Z2, Dual.C_val, Dual.C_eps, Dual.pow_eq] using h
  -- Compute `aX.eval₂ Dual.C Z2 = ⟨S_K / B, 1⟩` and `bX.eval₂ Dual.C Z2 = ⟨Q_K / B, (5*S_K - 3*Q_K)/(6*S_K)⟩`!
  set d_ab : K5 := 6 * S_K * B
  have h6_ne : (6 : K5) ≠ 0 := by exact_mod_cast (by decide : (6 : ℕ) ≠ 0)
  have hd_ab_ne : d_ab ≠ 0 := mul_ne_zero (mul_ne_zero h6_ne hS) hB
  set inv_d : K5 := d_ab⁻¹
  have hd_inv : d_ab * inv_d = 1 := mul_inv_cancel₀ hd_ab_ne
  set a_du : Dual K5 := Dual.C inv_d * ⟨6 * S_K ^ 2, 6 * S_K * B⟩
  set b_du : Dual K5 := Dual.C inv_d * ⟨6 * S_K * Q_K, (5 * S_K - 3 * Q_K) * B⟩
  have haX_Z2 : aX.eval₂ Dual.C Z2 = a_du := by
    ext
    · simp only [aX, Z2, a_du, eval₂_mul, eval₂_C, eval₂_X, Dual.C_val, Dual.mul_val, z2]
      apply mul_left_cancel₀ (mul_ne_zero hw0_ne hd_ab_ne)
      have h1 : w0 * d_ab * (1 / w0 * (w0 * S_K / B)) = 6 * S_K ^ 2 * w0 := by
        dsimp only [d_ab]; field_simp [hw0_ne, hB]
      have h2 : w0 * d_ab * (inv_d * (6 * S_K ^ 2)) = 6 * S_K ^ 2 * w0 := by
        linear_combination (w0 * (6 * S_K ^ 2)) * hd_inv
      rw [h1, h2]
    · simp only [aX, Z2, a_du, eval₂_mul, eval₂_C, eval₂_X, Dual.C_val, Dual.C_eps, Dual.mul_eps]
      rw [zero_mul, add_zero, one_div, inv_mul_cancel₀ hw0_ne, zero_mul, add_zero]
      have h : inv_d * (6 * S_K * B) = d_ab * inv_d := by dsimp only [d_ab]; ring
      rw [h, hd_inv]
  have hbX_Z2 : bX.eval₂ Dual.C Z2 = b_du := by
    have hca_cb : -ca0 / cb0 = (5 * S_K - 3 * Q_K) / (6 * S_K) := by
      apply mul_left_cancel₀ (mul_ne_zero hcb0_ne (mul_ne_zero h6_ne hS))
      have hl : cb0 * (6 * S_K) * (-ca0 / cb0) = -6 * S_K * ca0 := by field_simp [hcb0_ne]
      have hr : cb0 * (6 * S_K) * ((5 * S_K - 3 * Q_K) / (6 * S_K)) = cb0 * (5 * S_K - 3 * Q_K) := by
        field_simp [h6_ne, hS]
      rw [hl, hr]; dsimp only [ca0, cb0]; ring
    ext
    · simp only [bX, Z2, b_du, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, Dual.C_val, Dual.add_val, Dual.mul_val]
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hw0_ne hcb0_ne) hd_ab_ne)
      have hl : w0 * cb0 * d_ab * (-ca0 / (w0 * cb0) * z2 + -c0W0 / (w0 * cb0)) =
          -d_ab * (ca0 * z2 + c0W0) := by field_simp [hw0_ne, hcb0_ne]; ring
      have hr : w0 * cb0 * d_ab * (inv_d * (6 * S_K * Q_K)) = 6 * S_K * Q_K * w0 * cb0 := by
        linear_combination (w0 * cb0 * (6 * S_K * Q_K)) * hd_inv
      rw [hl, hr]
      have hw0_mul : B ^ 3 * w0 = -(25 / 4 : K5) * S_K * A ^ 2 := by
        rw [hw0_eq, mul_div_cancel₀ _ (pow_ne_zero 3 hB)]
      apply mul_left_cancel₀ (pow_ne_zero 2 hB)
      have h1 : B ^ 2 * (-d_ab * (ca0 * z2 + c0W0)) =
          -6 * S_K * B ^ 2 * ca0 * S_K * w0 - 6 * S_K * (c0W0 * B ^ 3) := by
        dsimp only [d_ab, z2]; field_simp [hB]; ring
      rw [h1]
      have hc0W : c0W0 * B ^ 3 = -(4 / 81 : K5) * B ^ 2 * w0 * (B ^ 3 * w0) := by
        simp only [c0W0, CoverParams.c0_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, B]; ring
      rw [hc0W, hw0_mul]
      dsimp only [ca0, cb0, A]; ring
    · simp only [bX, Z2, b_du, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, Dual.C_val, Dual.C_eps, Dual.add_eps, Dual.mul_eps]
      rw [zero_mul, add_zero, add_zero, zero_mul, add_zero]
      have h1 : -ca0 / (w0 * cb0) * w0 = -ca0 / cb0 := by field_simp [hw0_ne, hcb0_ne]
      rw [h1, hca_cb]
      apply mul_left_cancel₀ hd_ab_ne
      have h2 : d_ab * ((5 * S_K - 3 * Q_K) / (6 * S_K)) = (5 * S_K - 3 * Q_K) * B := by
        dsimp only [d_ab]; field_simp [h6_ne, hS]
      rw [h2]; linear_combination -((5 * S_K - 3 * Q_K) * B) * hd_inv
  -- Evaluate `P_A.eval₂ Dual.C Z2 = A0U_12_of Dual.C a_du b_du` by clearing `d_ab ^ 6` (division-free `ring`!)
  set Q_quad : K5 := 11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
    5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K
  have hPA_Z2 : P_A.eval₂ Dual.C Z2 = A0U_12_of Dual.C a_du b_du := by
    have h := map_A0U_12_of (Polynomial.eval₂RingHom Dual.C Z2) Polynomial.C aX bX
    have hcomp : (Polynomial.eval₂RingHom Dual.C Z2).comp Polynomial.C = Dual.C :=
      RingHom.ext (fun r => by simp)
    simpa only [P_A, hcomp, Polynomial.coe_eval₂RingHom, haX_Z2, hbX_Z2] using h
  have hA0U_Z2_val_eps :
      Dual.C (d_ab ^ 3) * (P_A.eval₂ Dual.C Z2) =
        ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
         -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ := by
    rw [hPA_Z2]
    exact br2_0_A0U_Z2_eval
  have hPQ_Z2 : Dual.C (35721 * d_ab) * (P_Q.eval₂ Dual.C Z2) =
      ⟨35721 * (q1_c0 * (6 * S_K ^ 2) + q1_c1 * (6 * S_K * Q_K) + q1_c2 * (6 * S_K * B)),
       35721 * (q1_c0 * (6 * S_K * B) + q1_c1 * ((5 * S_K - 3 * Q_K) * B))⟩ := by
    ext
    · simp only [P_Q, eval₂_add, eval₂_mul, eval₂_C, haX_Z2, hbX_Z2, a_du, b_du,
        Dual.C_val, Dual.add_val, Dual.mul_val]
      have h := hd_inv; dsimp only [d_ab] at h ⊢
      linear_combination (35721 * (q1_c0 * (6 * S_K ^ 2) + q1_c1 * (6 * S_K * Q_K))) * h
    · simp only [P_Q, eval₂_add, eval₂_mul, eval₂_C, haX_Z2, hbX_Z2, a_du, b_du,
        Dual.C_val, Dual.C_eps, Dual.add_eps, Dual.mul_eps, zero_mul, add_zero]
      linear_combination (35721 * (q1_c0 * (6 * S_K * B) + q1_c1 * ((5 * S_K - 3 * Q_K) * B))) * hd_inv
  have hPg0_Z2_prod : Dual.C (35721 * d_ab ^ 4) * (P_g0.eval₂ Dual.C Z2) =
      Dual.C (w0 ^ 2) *
        ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
         -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ *
        ⟨35721 * (q1_c0 * (6 * S_K ^ 2) + q1_c1 * (6 * S_K * Q_K) + q1_c2 * (6 * S_K * B)),
         35721 * (q1_c0 * (6 * S_K * B) + q1_c1 * ((5 * S_K - 3 * Q_K) * B))⟩ := by
    rw [← hA0U_Z2_val_eps, ← hPQ_Z2]
    simp only [P_g0, eval₂_mul, eval₂_C]
    rw [show Dual.C (35721 * d_ab ^ 4) = Dual.C (d_ab ^ 3) * Dual.C (35721 * d_ab) by
      rw [← map_mul]; congr 1; ring]
    ring
  exact HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_q1_cancel
    hw0_eq hw0_ne hden_ne hq2_ne hcd_eq hP_val hP_eps hPg0_Z2_prod

/-! ### Section 5: Master Theorem `residue_zero_eta` -/

theorem residue_zero_eta : CrossedRationalResidue.residue 0 CoverResidue.eta = toK5_RU := by
  change (ψ0 CoverResidue.eta).coeff (-1) = toK5_RU
  unfold CoverResidue.eta
  rw [map_trace_AC_eq_sum_branches ψ0 W1_0 W2_0 W1_0_eq_ψ0 W2_0_eq_ψ0 W1_W2_0_sum_ψ0,
    HahnSeries.coeff_add, HodgeComputer.SymmetricSexticResidual.Proof.localU0_br1_vanishes, zero_add, br2_0_eta_AC_coeff_neg_one]

end SymmetricSexticResidual.LocalResidueU0

theorem solution :
    CrossedRationalResidue.residue 0 SymmetricSexticResidual.CoverResidue.eta =
      SymmetricSexticResidual.LocalResidueU0.toK5_RU :=
  SymmetricSexticResidual.LocalResidueU0.residue_zero_eta
