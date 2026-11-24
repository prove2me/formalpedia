-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_g_lead
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T12:53:33.530875+00:00
-- url     : https://prove2.me/submissions/82ee9da9-7497-4d6c-90ab-fb26ac003f89

import Definitions.Def_HodgeComputerSSR_BranchHelpers
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_branch_jet_helpers

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  PolynomialEncoding.KroneckerCheck QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators LaurentSeries PowerSeries

private abbrev numM_ValDual_of := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.numM_ValDual
private abbrev A0U_ValDual_of := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.A0U_ValDual
private abbrev dual_minor_pair_eq_const := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.dual_minor_pair_const
private abbrev EB_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.EB_bilinear
private abbrev QY_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QY_bilinear
private abbrev QX_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QX_bilinear
private abbrev QX_num_01_sub_00_factor := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QX_num_01_sub_00

private lemma quad_mul_coeff1 {F : Type*} [Field F] [CharZero F] (p0 p1 p2 q0 q1 q2 : F) :
    p0 * q1 + p1 * q0 =
      (8 * ((p0 + p1 + p2) * (q0 + q1 + q2) - (p0 - p1 + p2) * (q0 - q1 + q2)) -
        ((p0 + 2 * p1 + 4 * p2) * (q0 + 2 * q1 + 4 * q2) -
         (p0 - 2 * p1 + 4 * p2) * (q0 - 2 * q1 + 4 * q2))) / 12 := by ring


private lemma numM_12_of_eq_interp (mi : Fin 10) (a b : K5) :
    numM_12_of (RingHom.id K5) mi a b =
      (8 * (numM mi a b (S_K - a * T_K) (Q_K - b * T_K) 1 1 -
            numM mi a b (S_K - a * T_K) (Q_K - b * T_K) (-1) 1) -
        (numM mi a b (S_K - a * T_K) (Q_K - b * T_K) 2 1 -
         numM mi a b (S_K - a * T_K) (Q_K - b * T_K) (-2) 1)) / 12 := by
  set ξS := S_K - a * T_K
  set ξQ := Q_K - b * T_K
  have hS_form (s q U : K5) :
      dH_dS s q U 1 = (dHS_12_of (RingHom.id K5) s q).val +
        (dHS_12_of (RingHom.id K5) s q).eps * U + (-(4 / 81 : K5) * (s - 3 * q) ^ 2) * U ^ 2 := by
    simp only [dH_dS, dHS_12_of, RingHom.id_apply]; ring
  have hQ_form (s q v0 U : K5) :
      dH_dQ s q v0 U 1 = (dHQ_12_of (RingHom.id K5) s q v0).val +
        (dHQ_12_of (RingHom.id K5) s q v0).eps * U + ((4 / 27 : K5) * (s - 3 * q) ^ 2) * U ^ 2 := by
    simp only [dH_dQ, dHQ_12_of, RingHom.id_apply]; ring
  set a2D := dHS_12_of (RingHom.id K5) a b
  set a0D := dHS_12_of (RingHom.id K5) ξS ξQ
  set a1D := dHS_12_of (RingHom.id K5) (a + ξS) (b + ξQ) - a2D - a0D
  set b2D := dHQ_12_of (RingHom.id K5) a b 0
  set b0D := dHQ_12_of (RingHom.id K5) ξS ξQ 1
  set b1D := dHQ_12_of (RingHom.id K5) (a + ξS) (b + ξQ) 0 - b2D - dHQ_12_of (RingHom.id K5) ξS ξQ 0 +
    ⟨0, (10 / 7 : K5) * b⟩
  set p2_2 : K5 := -(4 / 81 : K5) * (a - 3 * b) ^ 2
  set p0_2 : K5 := -(4 / 81 : K5) * (ξS - 3 * ξQ) ^ 2
  set p1_2 : K5 := -(4 / 81 : K5) * ((a + ξS) - 3 * (b + ξQ)) ^ 2 - p2_2 - p0_2
  set q2_2 : K5 := (4 / 27 : K5) * (a - 3 * b) ^ 2
  set q0_2 : K5 := (4 / 27 : K5) * (ξS - 3 * ξQ) ^ 2
  set q1_2 : K5 := (4 / 27 : K5) * ((a + ξS) - 3 * (b + ξQ)) ^ 2 - q2_2 - q0_2
  have ha2 (U : K5) : q1_a2 a b U 1 = a2D.val + a2D.eps * U + p2_2 * U ^ 2 := hS_form a b U
  have ha0 (U : K5) : q1_a0 ξS ξQ U 1 = a0D.val + a0D.eps * U + p0_2 * U ^ 2 := hS_form ξS ξQ U
  have ha1 (U : K5) : q1_a1 a b ξS ξQ U 1 = a1D.val + a1D.eps * U + p1_2 * U ^ 2 := by
    simp only [q1_a1, hS_form, a1D, Dual.sub_val, Dual.sub_eps, p1_2]; ring
  have hb2 (U : K5) : q2_b2 a b U 1 = b2D.val + b2D.eps * U + q2_2 * U ^ 2 := hQ_form a b 0 U
  have hb0 (U : K5) : q2_b0 ξS ξQ U 1 = b0D.val + b0D.eps * U + q0_2 * U ^ 2 := hQ_form ξS ξQ 1 U
  have hb1 (U : K5) : q2_b1 a b ξS ξQ U 1 = b1D.val + b1D.eps * U + q1_2 * U ^ 2 := by
    simp only [q2_b1, hQ_form, b1D, Dual.add_val, Dual.add_eps, Dual.sub_val, Dual.sub_eps, q1_2]; ring
  have hcomb (m2 m1 m0 : K5) :
      (1 / 16 : K5) * (m2 * (a1D * b0D - a0D * b1D).eps - m1 * (a2D * b0D - a0D * b2D).eps +
        m0 * (a2D * b1D - a1D * b2D).eps) =
      (8 * ((1 / 16 : K5) * (m2 * ((a1D.val + a1D.eps * 1 + p1_2 * 1 ^ 2) * (b0D.val + b0D.eps * 1 + q0_2 * 1 ^ 2) -
            (a0D.val + a0D.eps * 1 + p0_2 * 1 ^ 2) * (b1D.val + b1D.eps * 1 + q1_2 * 1 ^ 2)) -
          m1 * ((a2D.val + a2D.eps * 1 + p2_2 * 1 ^ 2) * (b0D.val + b0D.eps * 1 + q0_2 * 1 ^ 2) -
            (a0D.val + a0D.eps * 1 + p0_2 * 1 ^ 2) * (b2D.val + b2D.eps * 1 + q2_2 * 1 ^ 2)) +
          m0 * ((a2D.val + a2D.eps * 1 + p2_2 * 1 ^ 2) * (b1D.val + b1D.eps * 1 + q1_2 * 1 ^ 2) -
            (a1D.val + a1D.eps * 1 + p1_2 * 1 ^ 2) * (b2D.val + b2D.eps * 1 + q2_2 * 1 ^ 2))) -
        (1 / 16 : K5) * (m2 * ((a1D.val + a1D.eps * (-1) + p1_2 * (-1) ^ 2) * (b0D.val + b0D.eps * (-1) + q0_2 * (-1) ^ 2) -
            (a0D.val + a0D.eps * (-1) + p0_2 * (-1) ^ 2) * (b1D.val + b1D.eps * (-1) + q1_2 * (-1) ^ 2)) -
          m1 * ((a2D.val + a2D.eps * (-1) + p2_2 * (-1) ^ 2) * (b0D.val + b0D.eps * (-1) + q0_2 * (-1) ^ 2) -
            (a0D.val + a0D.eps * (-1) + p0_2 * (-1) ^ 2) * (b2D.val + b2D.eps * (-1) + q2_2 * (-1) ^ 2)) +
          m0 * ((a2D.val + a2D.eps * (-1) + p2_2 * (-1) ^ 2) * (b1D.val + b1D.eps * (-1) + q1_2 * (-1) ^ 2) -
            (a1D.val + a1D.eps * (-1) + p1_2 * (-1) ^ 2) * (b2D.val + b2D.eps * (-1) + q2_2 * (-1) ^ 2)))) -
       ((1 / 16 : K5) * (m2 * ((a1D.val + a1D.eps * 2 + p1_2 * 2 ^ 2) * (b0D.val + b0D.eps * 2 + q0_2 * 2 ^ 2) -
            (a0D.val + a0D.eps * 2 + p0_2 * 2 ^ 2) * (b1D.val + b1D.eps * 2 + q1_2 * 2 ^ 2)) -
          m1 * ((a2D.val + a2D.eps * 2 + p2_2 * 2 ^ 2) * (b0D.val + b0D.eps * 2 + q0_2 * 2 ^ 2) -
            (a0D.val + a0D.eps * 2 + p0_2 * 2 ^ 2) * (b2D.val + b2D.eps * 2 + q2_2 * 2 ^ 2)) +
          m0 * ((a2D.val + a2D.eps * 2 + p2_2 * 2 ^ 2) * (b1D.val + b1D.eps * 2 + q1_2 * 2 ^ 2) -
            (a1D.val + a1D.eps * 2 + p1_2 * 2 ^ 2) * (b2D.val + b2D.eps * 2 + q2_2 * 2 ^ 2))) -
        (1 / 16 : K5) * (m2 * ((a1D.val + a1D.eps * (-2) + p1_2 * (-2) ^ 2) * (b0D.val + b0D.eps * (-2) + q0_2 * (-2) ^ 2) -
            (a0D.val + a0D.eps * (-2) + p0_2 * (-2) ^ 2) * (b1D.val + b1D.eps * (-2) + q1_2 * (-2) ^ 2)) -
          m1 * ((a2D.val + a2D.eps * (-2) + p2_2 * (-2) ^ 2) * (b0D.val + b0D.eps * (-2) + q0_2 * (-2) ^ 2) -
            (a0D.val + a0D.eps * (-2) + p0_2 * (-2) ^ 2) * (b2D.val + b2D.eps * (-2) + q2_2 * (-2) ^ 2)) +
          m0 * ((a2D.val + a2D.eps * (-2) + p2_2 * (-2) ^ 2) * (b1D.val + b1D.eps * (-2) + q1_2 * (-2) ^ 2) -
            (a1D.val + a1D.eps * (-2) + p1_2 * (-2) ^ 2) * (b2D.val + b2D.eps * (-2) + q2_2 * (-2) ^ 2))))) / 12 := by
    simp only [Dual.sub_eps, Dual.mul_eps]
    ring
  fin_cases mi <;> (
    simp only [numM_12_of, numM, ha2, ha1, ha0, hb2, hb1, hb0, RingHom.id_apply]
    exact hcomb _ _ _)


private lemma br2_0_numM_bounds
    {a_s b_s U V : LaurentSeries K5} {a0 b0 w0 : K5}
    (hw0_ne : w0 ≠ 0)
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead (-1) V w0) :
    let ξS_s := HahnSeries.C S_K - a_s * HahnSeries.C T_K
    let ξQ_s := HahnSeries.C Q_K - b_s * HahnSeries.C T_K
    ValLead (-2) (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (w0 ^ 2 * A0U_12_of (RingHom.id K5) a0 b0) ∧
    HasValGe (-2) (A_Y a_s b_s ξS_s ξQ_s U V) ∧
    HasValGe (-1) (A_X a_s b_s ξS_s ξQ_s U V) := by
  let dHS_D : K5 → K5 → Dual K5 := fun s q =>
    ⟨-(25 / 243 : K5) * (5 * s - 9 * q) * (15 * s - 9 * q) * w0,
     ((143 / 81 : K5) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2) * w0⟩
  let dHQ_D : K5 → K5 → K5 → Dual K5 := fun s q v0 =>
    ⟨(50 / 27 : K5) * s * (5 * s - 9 * q) * w0,
     (-(92 / 27 : K5) * s ^ 2 + (104 / 9) * s * q - (22 / 3) * q ^ 2 +
      (10 / 7) * q * v0 + (10 / 7) * v0 ^ 2) * w0⟩
  let numM_D : Fin 10 → K5 → K5 → Dual K5 := fun mi a b =>
    let ξS := S_K - a * T_K; let ξQ := Q_K - b * T_K
    let a2 := dHS_D a b; let a0 := dHS_D ξS ξQ
    let a1 := dHS_D (a + ξS) (b + ξQ) - a2 - a0
    let b2 := dHQ_D a b 0; let b0 := dHQ_D ξS ξQ 1
    let b1 := dHQ_D (a + ξS) (b + ξQ) 0 - b2 - dHQ_D ξS ξQ 0 + ⟨0, (10 / 7 : K5) * b * w0⟩
    let d20 := a2 * b0 - a0 * b2; let d21 := a2 * b1 - a1 * b2; let d10 := a1 * b0 - a0 * b1
    let (m2, m1, m0) : K5 × K5 × K5 := match mi with
      | 0 => (a ^ 2, 2 * a * ξS, ξS ^ 2)
      | 1 => (a * b, a * ξQ + b * ξS, ξS * ξQ)
      | 2 => (b ^ 2, 2 * b * ξQ, ξQ ^ 2)
      | 3 => (a, ξS, 0)
      | 4 => (0, a, ξS)
      | 5 => (b, ξQ, 0)
      | 6 => (0, b, ξQ)
      | 7 => (1, 0, 0)
      | 8 => (0, 1, 0)
      | 9 => (0, 0, 1)
    Dual.C (1 / 16 : K5) * (Dual.C m2 * d10 - Dual.C m1 * d20 + Dual.C m0 * d21)
  let A0U_D : K5 → K5 → Dual K5 := fun a b =>
    let m := fun i => numM_D i a b
    Dual.C (-(19708 / 1257375 : K5)) * (5 * m 0 - 9 * m 1) +
    Dual.C (1472 / 1257375 : K5) * (5 * m 1 - 9 * m 2) -
    Dual.C (16 / 729 : K5) * (5 * m 3 - 9 * m 5) +
    Dual.C (188 / 2025 : K5) * (5 * m 4 - 9 * m 6)
  intro ξS_s ξQ_s
  have ha_D : ValDual 0 a_s ⟨a0, a_s.coeff 1⟩ := ⟨ha_L.val, ha_L.c0, rfl⟩
  have hb_D : ValDual 0 b_s ⟨b0, b_s.coeff 1⟩ := ⟨hb_L.val, hb_L.c0, rfl⟩
  have hV_D : ValDual (-1) V ⟨w0, V.coeff 0⟩ := ⟨hV_L.val, hV_L.c0, rfl⟩
  have hξS_D : ValDual 0 ξS_s ⟨S_K - a0 * T_K, -a_s.coeff 1 * T_K⟩ :=
    ((ValDual.of_C S_K).sub ((ha_D.mul (ValDual.of_C T_K)).eq_k (by omega))).eq_d
      (by ext <;> simp [Dual.C])
  have hξQ_D : ValDual 0 ξQ_s ⟨Q_K - b0 * T_K, -b_s.coeff 1 * T_K⟩ :=
    ((ValDual.of_C Q_K).sub ((hb_D.mul (ValDual.of_C T_K)).eq_k (by omega))).eq_d
      (by ext <;> simp [Dual.C])
  -- Generic `ValDual (-1)` for `dH_dS` and `dH_dQ` at `U = t, V = w0*t^{-1} + v1`!
  let dHS_gen : Dual K5 → Dual K5 → Dual K5 := fun sD qD =>
    Dual.C (-(25 / 243 : K5)) * (5 * sD - 9 * qD) * (15 * sD - 9 * qD) * ⟨w0, V.coeff 0⟩ +
    ⟨0, ((143 / 81 : K5) * sD.val ^ 2 - (184 / 27) * sD.val * qD.val + (52 / 9) * qD.val ^ 2) * w0⟩
  let dHQ_gen : Dual K5 → Dual K5 → K5 → Dual K5 := fun sD qD v0 =>
    Dual.C (50 / 27 : K5) * sD * (5 * sD - 9 * qD) * ⟨w0, V.coeff 0⟩ +
    ⟨0, (-(92 / 27 : K5) * sD.val ^ 2 + (104 / 9) * sD.val * qD.val - (22 / 3) * qD.val ^ 2 +
      (10 / 7) * qD.val * v0 + (10 / 7) * v0 ^ 2) * w0⟩
  have hdHS_VD {s q : LaurentSeries K5} {sD qD : Dual K5} (hs : ValDual 0 s sD) (hq : ValDual 0 q qD) :
      ValDual (-1) (dH_dS s q U V) (dHS_gen sD qD) := by
    unfold dH_dS
    have h1 : HasValGe 1 (-(4 / 81 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by
      rw [show -(4 / 81 : LaurentSeries K5) = HahnSeries.C (-(4 / 81 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]
      have hsq : HasValGe 0 ((s - 3 * q) ^ 2) :=
        ((hs.val.sub ((HasValGe.of_nat 3).mul hq.val |>.mono (by omega))).pow 2).mono (by omega)
      exact ((((HasValGe.of_C _).mul hsq).mul (hU_L.val.pow 2)).mul hV_L.val).mono (by omega)
    have h2 : ValLead 0 (((143 / 81 : LaurentSeries K5) * s ^ 2 - (184 / 27) * s * q +
        (52 / 9) * q ^ 2) * U * V)
        (((143 / 81 : K5) * sD.val ^ 2 - (184 / 27) * sD.val * qD.val + (52 / 9) * qD.val ^ 2) * w0) := by
      have ha : ValLead 0 ((143 / 81 : LaurentSeries K5) * s ^ 2) ((143 / 81 : K5) * sD.val ^ 2) := by
        rw [show (143 / 81 : LaurentSeries K5) = HahnSeries.C (143 / 81 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((ValLead.of_C _).mul (hs.toValLead.pow 2)).eq_k (by omega)
      have hb : ValLead 0 ((184 / 27 : LaurentSeries K5) * s * q) ((184 / 27 : K5) * sD.val * qD.val) := by
        rw [show (184 / 27 : LaurentSeries K5) = HahnSeries.C (184 / 27 : K5) by simp only [map_div₀, map_ofNat]]
        exact (((ValLead.of_C _).mul hs.toValLead).mul hq.toValLead).eq_k (by omega)
      have hc : ValLead 0 ((52 / 9 : LaurentSeries K5) * q ^ 2) ((52 / 9 : K5) * qD.val ^ 2) := by
        rw [show (52 / 9 : LaurentSeries K5) = HahnSeries.C (52 / 9 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((ValLead.of_C _).mul (hq.toValLead.pow 2)).eq_k (by omega)
      exact ((((ha.sub hb).add hc).mul hU_L).mul hV_L).eq_k (by omega) |>.eq_c (by ring)
    have h3 : ValDual (-1) (-(25 / 243 : LaurentSeries K5) * (5 * s - 9 * q) * (15 * s - 9 * q) * V)
        (Dual.C (-(25 / 243 : K5)) * (5 * sD - 9 * qD) * (15 * sD - 9 * qD) * ⟨w0, V.coeff 0⟩) := by
      have hc : ValDual 0 (-(25 / 243 : LaurentSeries K5)) (Dual.C (-(25 / 243 : K5))) := by
        rw [show -(25 / 243 : LaurentSeries K5) = HahnSeries.C (-(25 / 243 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]; exact ValDual.of_C _
      have hl1 : ValDual 0 (5 * s - 9 * q) (5 * sD - 9 * qD) :=
        (((ValDual.of_nat 5).mul hs).eq_k (by omega)).sub (((ValDual.of_nat 9).mul hq).eq_k (by omega))
      have hl2 : ValDual 0 (15 * s - 9 * q) (15 * sD - 9 * qD) :=
        (((ValDual.of_nat 15).mul hs).eq_k (by omega)).sub (((ValDual.of_nat 9).mul hq).eq_k (by omega))
      exact (((hc.mul hl1).mul hl2).mul hV_D).eq_k (by omega)
    have hre : -(4 / 81 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V +
        ((143 / 81) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2) * U * V -
        (25 / 243) * (5 * s - 9 * q) * (15 * s - 9 * q) * V =
        (-(25 / 243) * (5 * s - 9 * q) * (15 * s - 9 * q) * V +
         ((143 / 81) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2) * U * V) +
        (-(4 / 81) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by ring
    rw [hre]
    exact (h3.add_shift1 h2).add_high h1
  have hdHQ_VD {s q : LaurentSeries K5} {sD qD : Dual K5} {v0 : K5} (hs : ValDual 0 s sD) (hq : ValDual 0 q qD) :
      ValDual (-1) (dH_dQ s q (HahnSeries.C v0) U V) (dHQ_gen sD qD v0) := by
    unfold dH_dQ
    have h1 : HasValGe 1 ((4 / 27 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by
      rw [show (4 / 27 : LaurentSeries K5) = HahnSeries.C (4 / 27 : K5) by simp only [map_div₀, map_ofNat]]
      have hsq : HasValGe 0 ((s - 3 * q) ^ 2) :=
        ((hs.val.sub ((HasValGe.of_nat 3).mul hq.val |>.mono (by omega))).pow 2).mono (by omega)
      exact ((((HasValGe.of_C _).mul hsq).mul (hU_L.val.pow 2)).mul hV_L.val).mono (by omega)
    have h2 : ValLead 0 ((-(92 / 27 : LaurentSeries K5) * s ^ 2 + (104 / 9) * s * q -
        (22 / 3) * q ^ 2 + (10 / 7) * q * HahnSeries.C v0 + (10 / 7) * HahnSeries.C v0 ^ 2) * U * V)
        ((-(92 / 27 : K5) * sD.val ^ 2 + (104 / 9) * sD.val * qD.val - (22 / 3) * qD.val ^ 2 +
          (10 / 7) * qD.val * v0 + (10 / 7) * v0 ^ 2) * w0) := by
      have ha : ValLead 0 (-(92 / 27 : LaurentSeries K5) * s ^ 2) (-(92 / 27 : K5) * sD.val ^ 2) := by
        rw [show -(92 / 27 : LaurentSeries K5) = HahnSeries.C (-(92 / 27 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]
        exact ((ValLead.of_C _).mul (hs.toValLead.pow 2)).eq_k (by omega)
      have hb : ValLead 0 ((104 / 9 : LaurentSeries K5) * s * q) ((104 / 9 : K5) * sD.val * qD.val) := by
        rw [show (104 / 9 : LaurentSeries K5) = HahnSeries.C (104 / 9 : K5) by simp only [map_div₀, map_ofNat]]
        exact (((ValLead.of_C _).mul hs.toValLead).mul hq.toValLead).eq_k (by omega)
      have hc : ValLead 0 ((22 / 3 : LaurentSeries K5) * q ^ 2) ((22 / 3 : K5) * qD.val ^ 2) := by
        rw [show (22 / 3 : LaurentSeries K5) = HahnSeries.C (22 / 3 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((ValLead.of_C _).mul (hq.toValLead.pow 2)).eq_k (by omega)
      have hd : ValLead 0 ((10 / 7 : LaurentSeries K5) * q * HahnSeries.C v0) ((10 / 7 : K5) * qD.val * v0) := by
        rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
        exact (((ValLead.of_C _).mul hq.toValLead).mul (ValLead.of_C v0)).eq_k (by omega)
      have he : ValLead 0 ((10 / 7 : LaurentSeries K5) * HahnSeries.C v0 ^ 2) ((10 / 7 : K5) * v0 ^ 2) := by
        rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((ValLead.of_C _).mul ((ValLead.of_C v0).pow 2)).eq_k (by omega)
      exact ((((((ha.add hb).sub hc).add hd).add he).mul hU_L).mul hV_L).eq_k (by omega) |>.eq_c (by ring)
    have h3 : ValDual (-1) ((50 / 27 : LaurentSeries K5) * s * (5 * s - 9 * q) * V)
        (Dual.C (50 / 27 : K5) * sD * (5 * sD - 9 * qD) * ⟨w0, V.coeff 0⟩) := by
      have hc : ValDual 0 (50 / 27 : LaurentSeries K5) (Dual.C (50 / 27 : K5)) := by
        rw [show (50 / 27 : LaurentSeries K5) = HahnSeries.C (50 / 27 : K5) by simp only [map_div₀, map_ofNat]]; exact ValDual.of_C _
      have hl1 : ValDual 0 (5 * s - 9 * q) (5 * sD - 9 * qD) :=
        (((ValDual.of_nat 5).mul hs).eq_k (by omega)).sub (((ValDual.of_nat 9).mul hq).eq_k (by omega))
      exact (((hc.mul hs).mul hl1).mul hV_D).eq_k (by omega)
    have hre : (4 / 27 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V +
        (-(92 / 27) * s ^ 2 + (104 / 9) * s * q - (22 / 3) * q ^ 2 +
          (10 / 7) * q * HahnSeries.C v0 + (10 / 7) * HahnSeries.C v0 ^ 2) * U * V +
        (50 / 27) * s * (5 * s - 9 * q) * V =
        ((50 / 27) * s * (5 * s - 9 * q) * V +
         (-(92 / 27) * s ^ 2 + (104 / 9) * s * q - (22 / 3) * q ^ 2 +
          (10 / 7) * q * HahnSeries.C v0 + (10 / 7) * HahnSeries.C v0 ^ 2) * U * V) +
        ((4 / 27) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by ring
    rw [hre]
    exact (h3.add_shift1 h2).add_high h1
  -- Every `numM i` has `ValDual (-2)` (and hence `HasValGe (-2)`)!
  let aD : Dual K5 := ⟨a0, a_s.coeff 1⟩
  let bD : Dual K5 := ⟨b0, b_s.coeff 1⟩
  let ξSD : Dual K5 := ⟨S_K - a0 * T_K, -a_s.coeff 1 * T_K⟩
  let ξQD : Dual K5 := ⟨Q_K - b0 * T_K, -b_s.coeff 1 * T_K⟩
  let a2_g : Dual K5 := dHS_gen aD bD
  let a0_g : Dual K5 := dHS_gen ξSD ξQD
  let a1_g : Dual K5 := dHS_gen (aD + ξSD) (bD + ξQD) - a2_g - a0_g
  let b2_g : Dual K5 := dHQ_gen aD bD 0
  let b0_g : Dual K5 := dHQ_gen ξSD ξQD 1
  let b1_g : Dual K5 := dHQ_gen (aD + ξSD) (bD + ξQD) 0 - b2_g - dHQ_gen ξSD ξQD 0 + ⟨0, (10 / 7 : K5) * b0 * w0⟩
  let d20_g : Dual K5 := a2_g * b0_g - a0_g * b2_g
  let d21_g : Dual K5 := a2_g * b1_g - a1_g * b2_g
  let d10_g : Dual K5 := a1_g * b0_g - a0_g * b1_g
  let numM_gen : Fin 10 → Dual K5 := fun mi =>
    let (m2, m1, m0) : Dual K5 × Dual K5 × Dual K5 := match mi with
      | 0 => (aD ^ 2, 2 * aD * ξSD, ξSD ^ 2)
      | 1 => (aD * bD, aD * ξQD + bD * ξSD, ξSD * ξQD)
      | 2 => (bD ^ 2, 2 * bD * ξQD, ξQD ^ 2)
      | 3 => (aD, ξSD, 0)
      | 4 => (0, aD, ξSD)
      | 5 => (bD, ξQD, 0)
      | 6 => (0, bD, ξQD)
      | 7 => (1, 0, 0)
      | 8 => (0, 1, 0)
      | 9 => (0, 0, 1)
    Dual.C (1 / 16 : K5) * (m2 * d10_g - m1 * d20_g + m0 * d21_g)
  have hnumM_VD (mi : Fin 10) : ValDual (-2) (numM mi a_s b_s ξS_s ξQ_s U V) (numM_gen mi) := by
    have ha2 : ValDual (-1) (q1_a2 a_s b_s U V) a2_g := hdHS_VD ha_D hb_D
    have ha0 : ValDual (-1) (q1_a0 ξS_s ξQ_s U V) a0_g := hdHS_VD hξS_D hξQ_D
    have ha1 : ValDual (-1) (q1_a1 a_s b_s ξS_s ξQ_s U V) a1_g :=
      ((hdHS_VD (ha_D.add hξS_D) (hb_D.add hξQ_D)).sub ha2).sub ha0
    have hb2 : ValDual (-1) (q2_b2 a_s b_s U V) b2_g := by
      unfold q2_b2; simpa only [map_zero] using hdHQ_VD (v0 := 0) ha_D hb_D
    have hb0 : ValDual (-1) (q2_b0 ξS_s ξQ_s U V) b0_g := by
      unfold q2_b0; simpa only [map_one] using hdHQ_VD (v0 := 1) hξS_D hξQ_D
    have hb1 : ValDual (-1) (q2_b1 a_s b_s ξS_s ξQ_s U V) b1_g := by
      unfold q2_b1
      have hbase := ((hdHQ_VD (v0 := 0) (ha_D.add hξS_D) (hb_D.add hξQ_D)).sub
        (hdHQ_VD (v0 := 0) ha_D hb_D)).sub (hdHQ_VD (v0 := 0) hξS_D hξQ_D)
      have hbase' : ValDual (-1) (dH_dQ (a_s + ξS_s) (b_s + ξQ_s) 0 U V - dH_dQ a_s b_s 0 U V -
          dH_dQ ξS_s ξQ_s 0 U V) (dHQ_gen (aD + ξSD) (bD + ξQD) 0 - b2_g - dHQ_gen ξSD ξQD 0) := by
        simpa only [map_zero] using hbase
      have hextra : ValLead 0 ((10 / 7 : LaurentSeries K5) * b_s * U * V) ((10 / 7 : K5) * b0 * w0) := by
        rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((((ValLead.of_C _).mul hb_D.toValLead).mul hU_L).mul hV_L).eq_k (by omega) |>.eq_c (by ring)
      exact hbase'.add_shift1 hextra
    exact (numM_ValDual_of ha_D hb_D hξS_D hξQ_D ha2 ha1 ha0 hb2 hb1 hb0 mi).eq_k (k' := -2) (by omega)
  -- Every pair `5 * numM_gen i - 9 * numM_gen j` for `(0,1), (1,2), (3,5), (4,6)` equals
  -- `⟨0, (5 * numM_D i a0 b0 - 9 * numM_D j a0 b0).eps⟩` (independent of `a1, b1, V.coeff 0`)!
  set ξS0 : K5 := S_K - a0 * T_K
  set ξQ0 : K5 := Q_K - b0 * T_K
  set a1_D : Dual K5 := dHS_D (a0 + ξS0) (b0 + ξQ0) - dHS_D a0 b0 - dHS_D ξS0 ξQ0
  set b1_D : Dual K5 := dHQ_D (a0 + ξS0) (b0 + ξQ0) 0 - dHQ_D a0 b0 0 - dHQ_D ξS0 ξQ0 0 + ⟨0, (10 / 7 : K5) * b0 * w0⟩
  set d20_D : Dual K5 := dHS_D a0 b0 * dHQ_D ξS0 ξQ0 1 - dHS_D ξS0 ξQ0 * dHQ_D a0 b0 0
  set d21_D : Dual K5 := dHS_D a0 b0 * b1_D - a1_D * dHQ_D a0 b0 0
  set d10_D : Dual K5 := a1_D * dHQ_D ξS0 ξQ0 1 - dHS_D ξS0 ξQ0 * b1_D
  have hnumM_D_eq (mi : Fin 10) : numM_D mi a0 b0 =
      let (m2, m1, m0) : K5 × K5 × K5 := match mi with
        | 0 => (a0 ^ 2, 2 * a0 * ξS0, ξS0 ^ 2)
        | 1 => (a0 * b0, a0 * ξQ0 + b0 * ξS0, ξS0 * ξQ0)
        | 2 => (b0 ^ 2, 2 * b0 * ξQ0, ξQ0 ^ 2)
        | 3 => (a0, ξS0, 0)
        | 4 => (0, a0, ξS0)
        | 5 => (b0, ξQ0, 0)
        | 6 => (0, b0, ξQ0)
        | 7 => (1, 0, 0)
        | 8 => (0, 1, 0)
        | 9 => (0, 0, 1)
      Dual.C (1 / 16 : K5) * (Dual.C m2 * d10_D - Dual.C m1 * d20_D + Dual.C m0 * d21_D) := rfl
  have hpair_eq (u1 u0 : Dual K5) :
      Dual.C (1 / 16 : K5) *
        ((u1 * (5 * aD - 9 * bD)) * d10_g - (u1 * (5 * ξSD - 9 * ξQD) + u0 * (5 * aD - 9 * bD)) * d20_g +
         (u0 * (5 * ξSD - 9 * ξQD)) * d21_g) =
      ⟨0, (Dual.C (1 / 16 : K5) *
        (Dual.C (u1.val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C (u1.val * (5 * ξS0 - 9 * ξQ0) + u0.val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C (u0.val * (5 * ξS0 - 9 * ξQ0)) * d21_D)).eps⟩ := by
    set wD : Dual K5 := ⟨w0, V.coeff 0⟩
    set dHS0 : Dual K5 → Dual K5 → Dual K5 := fun s q => Dual.C (-(25 / 243 : K5)) * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
    set dHQ0 : Dual K5 → Dual K5 → Dual K5 := fun s q => Dual.C (50 / 27 : K5) * s * (5 * s - 9 * q) * wD
    set dHS0_C : Dual K5 → Dual K5 → Dual K5 := fun s q => Dual.C (-(25 / 243 : K5)) * (5 * s - 9 * q) * (15 * s - 9 * q) * Dual.C w0
    set dHQ0_C : Dual K5 → Dual K5 → Dual K5 := fun s q => Dual.C (50 / 27 : K5) * s * (5 * s - 9 * q) * Dual.C w0
    set da2 := (dHS_D a0 b0).eps
    set da0 := (dHS_D ξS0 ξQ0).eps
    set da1 := (dHS_D (a0 + ξS0) (b0 + ξQ0) - dHS_D a0 b0 - dHS_D ξS0 ξQ0).eps
    set db2 := (dHQ_D a0 b0 0).eps
    set db0 := (dHQ_D ξS0 ξQ0 1).eps
    set db1 := (dHQ_D (a0 + ξS0) (b0 + ξQ0) 0 - dHQ_D a0 b0 0 - dHQ_D ξS0 ξQ0 0 + ⟨0, (10 / 7 : K5) * b0 * w0⟩).eps
    have ha2_g : a2_g = dHS0 aD bD + ⟨0, da2⟩ := rfl
    have ha0_g : a0_g = dHS0 ξSD ξQD + ⟨0, da0⟩ := rfl
    have ha1_g : a1_g = (dHS0 (aD + ξSD) (bD + ξQD) - dHS0 aD bD - dHS0 ξSD ξQD) + ⟨0, da1⟩ := by
      ext <;> simp only [a1_g, a2_g, a0_g, dHS_gen, dHS0, dHS_D, da1, aD, bD, ξSD, ξQD, wD, ξS0, ξQ0,
        Dual.add_val, Dual.sub_val, Dual.add_eps, Dual.sub_eps] <;> ring
    have hb2_g : b2_g = dHQ0 aD bD + ⟨0, db2⟩ := rfl
    have hb0_g : b0_g = dHQ0 ξSD ξQD + ⟨0, db0⟩ := rfl
    have hb1_g : b1_g = (dHQ0 (aD + ξSD) (bD + ξQD) - dHQ0 aD bD - dHQ0 ξSD ξQD) + ⟨0, db1⟩ := by
      ext <;> simp only [b1_g, b2_g, dHQ_gen, dHQ0, dHQ_D, db1, aD, bD, ξSD, ξQD, wD, ξS0, ξQ0,
        Dual.add_val, Dual.sub_val, Dual.add_eps, Dual.sub_eps] <;> ring
    have hdS0_C (s q : K5) :
        dHS0_C (Dual.C s) (Dual.C q) = Dual.C (-(25 / 243 : K5) * (5 * s - 9 * q) * (15 * s - 9 * q) * w0) := by
      simp only [dHS0_C, map_mul, map_sub, map_ofNat]
    have hdQ0_C (s q : K5) :
        dHQ0_C (Dual.C s) (Dual.C q) = Dual.C ((50 / 27 : K5) * s * (5 * s - 9 * q) * w0) := by
      simp only [dHQ0_C, map_mul, map_sub, map_ofNat]
    have ha2_D : dHS_D a0 b0 = dHS0_C (Dual.C a0) (Dual.C b0) + ⟨0, da2⟩ := by
      rw [hdS0_C]; ext <;> simp only [dHS_D, da2, Dual.add_val, Dual.C_val, Dual.add_eps, Dual.C_eps] <;> ring
    have ha0_D : dHS_D ξS0 ξQ0 = dHS0_C (Dual.C ξS0) (Dual.C ξQ0) + ⟨0, da0⟩ := by
      rw [hdS0_C]; ext <;> simp only [dHS_D, da0, Dual.add_val, Dual.C_val, Dual.add_eps, Dual.C_eps] <;> ring
    have ha1_D : a1_D =
        (dHS0_C (Dual.C a0 + Dual.C ξS0) (Dual.C b0 + Dual.C ξQ0) -
          dHS0_C (Dual.C a0) (Dual.C b0) - dHS0_C (Dual.C ξS0) (Dual.C ξQ0)) + ⟨0, da1⟩ := by
      dsimp only [a1_D]
      rw [← map_add Dual.C, ← map_add Dual.C, hdS0_C, hdS0_C, hdS0_C]
      ext <;> simp only [dHS_D, da1, Dual.add_val, Dual.sub_val, Dual.C_val, Dual.add_eps, Dual.sub_eps, Dual.C_eps] <;> ring
    have hb2_D : dHQ_D a0 b0 0 = dHQ0_C (Dual.C a0) (Dual.C b0) + ⟨0, db2⟩ := by
      rw [hdQ0_C]; ext <;> simp only [dHQ_D, db2, Dual.add_val, Dual.C_val, Dual.add_eps, Dual.C_eps] <;> ring
    have hb0_D : dHQ_D ξS0 ξQ0 1 = dHQ0_C (Dual.C ξS0) (Dual.C ξQ0) + ⟨0, db0⟩ := by
      rw [hdQ0_C]; ext <;> simp only [dHQ_D, db0, Dual.add_val, Dual.C_val, Dual.add_eps, Dual.C_eps] <;> ring
    have hb1_D : b1_D =
        (dHQ0_C (Dual.C a0 + Dual.C ξS0) (Dual.C b0 + Dual.C ξQ0) -
          dHQ0_C (Dual.C a0) (Dual.C b0) - dHQ0_C (Dual.C ξS0) (Dual.C ξQ0)) + ⟨0, db1⟩ := by
      dsimp only [b1_D]
      rw [← map_add Dual.C, ← map_add Dual.C, hdQ0_C, hdQ0_C, hdQ0_C]
      ext <;> simp only [dHQ_D, db1, Dual.add_val, Dual.sub_val, Dual.C_val, Dual.add_eps, Dual.sub_eps, Dual.C_eps]; ring
    have hcore := dual_minor_pair_eq_const aD bD ξSD ξQD wD u1 u0 da2 da1 da0 db2 db1 db0
    dsimp only at hcore
    have hL : (u1 * (5 * aD - 9 * bD)) * d10_g - (u1 * (5 * ξSD - 9 * ξQD) + u0 * (5 * aD - 9 * bD)) * d20_g +
        (u0 * (5 * ξSD - 9 * ξQD)) * d21_g =
        ⟨0, (Dual.C (u1.val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C (u1.val * (5 * ξS0 - 9 * ξQ0) + u0.val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C (u0.val * (5 * ξS0 - 9 * ξQ0)) * d21_D).eps⟩ := by
      rw [show d10_g = a1_g * b0_g - a0_g * b1_g from rfl,
          show d20_g = a2_g * b0_g - a0_g * b2_g from rfl,
          show d21_g = a2_g * b1_g - a1_g * b2_g from rfl,
          show d10_D = a1_D * dHQ_D ξS0 ξQ0 1 - dHS_D ξS0 ξQ0 * b1_D from rfl,
          show d20_D = dHS_D a0 b0 * dHQ_D ξS0 ξQ0 1 - dHS_D ξS0 ξQ0 * dHQ_D a0 b0 0 from rfl,
          show d21_D = dHS_D a0 b0 * b1_D - a1_D * dHQ_D a0 b0 0 from rfl,
          ha2_g, ha1_g, ha0_g, hb2_g, hb1_g, hb0_g,
          ha1_D, ha2_D, ha0_D, hb1_D, hb2_D, hb0_D]
      have hm2C : Dual.C (u1.val * (5 * a0 - 9 * b0)) = Dual.C u1.val * (5 * Dual.C a0 - 9 * Dual.C b0) := by
        simp only [map_mul, map_sub, map_ofNat]
      have hm1C : Dual.C (u1.val * (5 * ξS0 - 9 * ξQ0) + u0.val * (5 * a0 - 9 * b0)) =
          Dual.C u1.val * (5 * Dual.C ξS0 - 9 * Dual.C ξQ0) + Dual.C u0.val * (5 * Dual.C a0 - 9 * Dual.C b0) := by
        simp only [map_add, map_mul, map_sub, map_ofNat]
      have hm0C : Dual.C (u0.val * (5 * ξS0 - 9 * ξQ0)) = Dual.C u0.val * (5 * Dual.C ξS0 - 9 * Dual.C ξQ0) := by
        simp only [map_mul, map_sub, map_ofNat]
      rw [hm2C, hm1C, hm0C]
      exact hcore
    rw [hL]
    ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps] <;> ring
  clear_value dHS_gen dHQ_gen a2_g a0_g a1_g b2_g b0_g b1_g d20_g d21_g d10_g a1_D b1_D d20_D d21_D d10_D
  have hp01_eq : 5 * numM_gen 0 - 9 * numM_gen 1 = ⟨0, (5 * numM_D 0 a0 b0 - 9 * numM_D 1 a0 b0).eps⟩ := by
    have h := hpair_eq aD ξSD
    have hL : 5 * numM_gen 0 - 9 * numM_gen 1 = Dual.C (1 / 16 : K5) *
        ((aD * (5 * aD - 9 * bD)) * d10_g - (aD * (5 * ξSD - 9 * ξQD) + ξSD * (5 * aD - 9 * bD)) * d20_g +
         (ξSD * (5 * ξSD - 9 * ξQD)) * d21_g) := by
      simp only [numM_gen]; ring
    have hR : 5 * numM_D 0 a0 b0 - 9 * numM_D 1 a0 b0 = Dual.C (1 / 16 : K5) *
        (Dual.C (aD.val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C (aD.val * (5 * ξS0 - 9 * ξQ0) + ξSD.val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C (ξSD.val * (5 * ξS0 - 9 * ξQ0)) * d21_D) := by
      rw [hnumM_D_eq 0, hnumM_D_eq 1]; dsimp only [aD, ξSD, ξS0, ξQ0]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]; ring
    rw [hL, hR]; exact h
  have hp12_eq : 5 * numM_gen 1 - 9 * numM_gen 2 = ⟨0, (5 * numM_D 1 a0 b0 - 9 * numM_D 2 a0 b0).eps⟩ := by
    have h := hpair_eq bD ξQD
    have hL : 5 * numM_gen 1 - 9 * numM_gen 2 = Dual.C (1 / 16 : K5) *
        ((bD * (5 * aD - 9 * bD)) * d10_g - (bD * (5 * ξSD - 9 * ξQD) + ξQD * (5 * aD - 9 * bD)) * d20_g +
         (ξQD * (5 * ξSD - 9 * ξQD)) * d21_g) := by
      simp only [numM_gen]; ring
    have hR : 5 * numM_D 1 a0 b0 - 9 * numM_D 2 a0 b0 = Dual.C (1 / 16 : K5) *
        (Dual.C (bD.val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C (bD.val * (5 * ξS0 - 9 * ξQ0) + ξQD.val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C (ξQD.val * (5 * ξS0 - 9 * ξQ0)) * d21_D) := by
      rw [hnumM_D_eq 1, hnumM_D_eq 2]; dsimp only [bD, ξQD, ξS0, ξQ0]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]; ring
    rw [hL, hR]; exact h
  have hp35_eq : 5 * numM_gen 3 - 9 * numM_gen 5 = ⟨0, (5 * numM_D 3 a0 b0 - 9 * numM_D 5 a0 b0).eps⟩ := by
    have h := hpair_eq 1 0
    have hL : 5 * numM_gen 3 - 9 * numM_gen 5 = Dual.C (1 / 16 : K5) *
        ((1 * (5 * aD - 9 * bD)) * d10_g - (1 * (5 * ξSD - 9 * ξQD) + 0 * (5 * aD - 9 * bD)) * d20_g +
         (0 * (5 * ξSD - 9 * ξQD)) * d21_g) := by
      simp only [numM_gen]; ring
    have hR : 5 * numM_D 3 a0 b0 - 9 * numM_D 5 a0 b0 = Dual.C (1 / 16 : K5) *
        (Dual.C ((1 : Dual K5).val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C ((1 : Dual K5).val * (5 * ξS0 - 9 * ξQ0) + (0 : Dual K5).val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C ((0 : Dual K5).val * (5 * ξS0 - 9 * ξQ0)) * d21_D) := by
      rw [hnumM_D_eq 3, hnumM_D_eq 5]; dsimp only [ξS0, ξQ0]
      simp only [Dual.one_val, Dual.zero_val, map_add, map_sub, map_mul, map_zero, map_one, map_ofNat]; ring
    rw [hL, hR]; exact h
  have hp46_eq : 5 * numM_gen 4 - 9 * numM_gen 6 = ⟨0, (5 * numM_D 4 a0 b0 - 9 * numM_D 6 a0 b0).eps⟩ := by
    have h := hpair_eq 0 1
    have hL : 5 * numM_gen 4 - 9 * numM_gen 6 = Dual.C (1 / 16 : K5) *
        ((0 * (5 * aD - 9 * bD)) * d10_g - (0 * (5 * ξSD - 9 * ξQD) + 1 * (5 * aD - 9 * bD)) * d20_g +
         (1 * (5 * ξSD - 9 * ξQD)) * d21_g) := by
      simp only [numM_gen]; ring
    have hR : 5 * numM_D 4 a0 b0 - 9 * numM_D 6 a0 b0 = Dual.C (1 / 16 : K5) *
        (Dual.C ((0 : Dual K5).val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C ((0 : Dual K5).val * (5 * ξS0 - 9 * ξQ0) + (1 : Dual K5).val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C ((1 : Dual K5).val * (5 * ξS0 - 9 * ξQ0)) * d21_D) := by
      rw [hnumM_D_eq 4, hnumM_D_eq 6]; dsimp only [ξS0, ξQ0]
      simp only [Dual.one_val, Dual.zero_val, map_add, map_sub, map_mul, map_zero, map_one, map_ofNat]; ring
    rw [hL, hR]; exact h
  have hA0U_L : ValLead (-1) (A_0U a_s b_s ξS_s ξQ_s U V) (A0U_D a0 b0).eps := by
    have hVD := A0U_ValDual_of hnumM_VD
    have heq_D : Dual.C (-(19708 / 1257375 : K5)) * (5 * numM_gen 0 - 9 * numM_gen 1) +
        Dual.C (1472 / 1257375 : K5) * (5 * numM_gen 1 - 9 * numM_gen 2) -
        Dual.C (16 / 729 : K5) * (5 * numM_gen 3 - 9 * numM_gen 5) +
        Dual.C (188 / 2025 : K5) * (5 * numM_gen 4 - 9 * numM_gen 6) = ⟨0, (A0U_D a0 b0).eps⟩ := by
      rw [hp01_eq, hp12_eq, hp35_eq, hp46_eq]
      ext <;> simp only [A0U_D, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.C_val,
        Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.C_eps] <;> ring
    rw [heq_D] at hVD
    exact ⟨hVD.val.inc hVD.c0, hVD.c1⟩
  -- `A_0V / V` has `HasValGe (-1)`, so `M0` has `ValLead (-2) M0 (A0U_D a0 b0).eps`!
  have hm_m2 (i : Fin 10) : HasValGe (-2) (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_VD i).val
  have hnat_m2 (n : ℕ) {f : LaurentSeries K5} (hf : HasValGe (-2) f) : HasValGe (-2) ((n : LaurentSeries K5) * f) :=
    ((HasValGe.of_nat n).mul hf).mono (by omega)
  have hp_m2 (i j : Fin 10) : HasValGe (-2) (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
    (hnat_m2 5 (hm_m2 i)).sub (hnat_m2 9 (hm_m2 j))
  have hA0V_m2 : HasValGe (-2) (A_0V a_s b_s ξS_s ξQ_s U V) := by
    unfold A_0V
    exact (((hasValGe_neg_div_nat_mul 892 3645 (hp_m2 3 4)).add
      (hasValGe_div_nat_mul 40 81 (hp_m2 5 6))).sub
      (hasValGe_div_nat_mul 112 2395 (hp_m2 7 8))).add
      (hasValGe_div_nat_mul 392 11975 (hp_m2 8 9))
  have hM0_L : ValLead (-2) (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (A0U_D a0 b0).eps := by
    have h1 := (hA0U_L.div_of_ne hU_L one_ne_zero).eq_k (k' := -2) (by omega) |>.eq_c (div_one _)
    have h2 : HasValGe (-1) (A_0V a_s b_s ξS_s ξQ_s U V / V) :=
      (hA0V_m2.div_of_lead_ne hV_L.val (hV_L.c0.symm ▸ hw0_ne)).1.mono (by omega)
    exact h1.add_high h2
  -- `A_Y` has `HasValGe (-2)` (because the `V` part multiplies `A_0U`-type combinations which have `HasValGe (-1)`!),
  -- and `A_X` has `HasValGe (-1)`!
  have hAY_m2 : HasValGe (-2) (A_Y a_s b_s ξS_s ξQ_s U V) := by
    unfold A_Y
    have ht1 : HasValGe (-2) (-(100 / 243 : LaurentSeries K5) *
        (25 * numM 3 a_s b_s ξS_s ξQ_s U V - 45 * numM 4 a_s b_s ξS_s ξQ_s U V -
         45 * numM 5 a_s b_s ξS_s ξQ_s U V + 81 * numM 6 a_s b_s ξS_s ξQ_s U V)) :=
      hasValGe_neg_div_nat_mul 100 243 ((((hnat_m2 25 (hm_m2 3)).sub (hnat_m2 45 (hm_m2 4))).sub
        (hnat_m2 45 (hm_m2 5))).add (hnat_m2 81 (hm_m2 6)))
    have ht2_inner : HasValGe (-1) (-(907876 / 33949125 : LaurentSeries K5) *
          (5 * numM 0 a_s b_s ξS_s ξQ_s U V - 9 * numM 1 a_s b_s ξS_s ξQ_s U V) +
        (2258324 / 33949125) * (5 * numM 1 a_s b_s ξS_s ξQ_s U V - 9 * numM 2 a_s b_s ξS_s ξQ_s U V) +
        (8 / 243) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 5 a_s b_s ξS_s ξQ_s U V) -
        (64 / 675) * (5 * numM 4 a_s b_s ξS_s ξQ_s U V - 9 * numM 6 a_s b_s ξS_s ξQ_s U V)) := by
      have hp1 (i j : Fin 10) (h0 : (5 * numM_gen i - 9 * numM_gen j).val = 0) :
          HasValGe (-1) (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) := by
        have h := (((ValDual.of_nat 5).mul (hnumM_VD i)).eq_k (k' := -2) (by omega)).sub
          (((ValDual.of_nat 9).mul (hnumM_VD j)).eq_k (k' := -2) (by omega))
        exact h.val.inc (by rw [h.c0]; simpa only [Nat.cast_ofNat] using h0)
      have hz01 : (5 * numM_gen 0 - 9 * numM_gen 1).val = 0 := by rw [hp01_eq]
      have hz12 : (5 * numM_gen 1 - 9 * numM_gen 2).val = 0 := by rw [hp12_eq]
      have hz35 : (5 * numM_gen 3 - 9 * numM_gen 5).val = 0 := by rw [hp35_eq]
      have hz46 : (5 * numM_gen 4 - 9 * numM_gen 6).val = 0 := by rw [hp46_eq]
      exact (((hasValGe_neg_div_nat_mul 907876 33949125 (hp1 0 1 hz01)).add
        (hasValGe_div_nat_mul 2258324 33949125 (hp1 1 2 hz12))).add
        (hasValGe_div_nat_mul 8 243 (hp1 3 5 hz35))).sub
        (hasValGe_div_nat_mul 64 675 (hp1 4 6 hz46))
    have ht2 := (hV_L.val.mul ht2_inner).mono (k2 := -2) (by omega)
    have ht3_inner : HasValGe (-2) (-(123236 / 24249375 : LaurentSeries K5) *
          (numM 0 a_s b_s ξS_s ξQ_s U V + (2790 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V +
           28 * numM 8 a_s b_s ξS_s ξQ_s U V - (5904 / 77) * numM 9 a_s b_s ξS_s ξQ_s U V) +
        (492944 / 33949125) * (numM 1 a_s b_s ξS_s ξQ_s U V +
          (927 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + (49 / 5) * numM 8 a_s b_s ξS_s ξQ_s U V -
          (21159 / 770) * numM 9 a_s b_s ξS_s ξQ_s U V)) :=
      (hasValGe_neg_div_nat_mul 123236 24249375
        ((((hm_m2 0).add (hasValGe_div_nat_mul 2790 77 (hm_m2 6))).add (hnat_m2 28 (hm_m2 8))).sub
          (hasValGe_div_nat_mul 5904 77 (hm_m2 9)))).add
      (hasValGe_div_nat_mul 492944 33949125
        ((((hm_m2 1).add (hasValGe_div_nat_mul 927 77 (hm_m2 6))).add (hasValGe_div_nat_mul 49 5 (hm_m2 8))).sub
          (hasValGe_div_nat_mul 21159 770 (hm_m2 9))))
    have ht3 := ((hU_L.val.mul hV_L.val).mul ht3_inner).mono (k2 := -2) (by omega)
    exact (ht1.add ht2).add ht3
  have hAX_m1 : HasValGe (-1) (A_X a_s b_s ξS_s ξQ_s U V) := by
    unfold A_X
    have hinner : HasValGe (-2) (-(8 / 405 : LaurentSeries K5) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 4 a_s b_s ξS_s ξQ_s U V) -
        (476 / 7185) * (5 * numM 7 a_s b_s ξS_s ξQ_s U V - 9 * numM 8 a_s b_s ξS_s ξQ_s U V) +
        (6916 / 35925) * (5 * numM 8 a_s b_s ξS_s ξQ_s U V - 9 * numM 9 a_s b_s ξS_s ξQ_s U V)) :=
      ((hasValGe_neg_div_nat_mul 8 405 (hp_m2 3 4)).sub (hasValGe_div_nat_mul 476 7185 (hp_m2 7 8))).add
        (hasValGe_div_nat_mul 6916 35925 (hp_m2 8 9))
    exact (hU_L.val.mul hinner).mono (by omega)
  have hA0U_D_eq (a b : K5) : (A0U_D a b).eps = w0 ^ 2 * A0U_12_of (RingHom.id K5) a b := by
    have hmi (mi : Fin 10) : (numM_D mi a b).eps = w0 ^ 2 * numM_12_of (RingHom.id K5) mi a b := by
      have hdHS (s q : K5) : dHS_D s q = Dual.C w0 * dHS_12_of (RingHom.id K5) s q := by
        ext <;> simp only [dHS_D, dHS_12_of, Dual.C_val, Dual.C_eps, Dual.mul_val, Dual.mul_eps, RingHom.id_apply] <;> ring
      have hdHQ (s q v0 : K5) : dHQ_D s q v0 = Dual.C w0 * dHQ_12_of (RingHom.id K5) s q v0 := by
        ext <;> simp only [dHQ_D, dHQ_12_of, Dual.C_val, Dual.C_eps, Dual.mul_val, Dual.mul_eps, RingHom.id_apply] <;> ring
      have hscale : ∀ (m2 m1 m0 : K5) (A2 A1 A0 B2 B1 B0 : Dual K5),
          (Dual.C (1 / 16 : K5) *
            (Dual.C m2 * ((Dual.C w0 * A1) * (Dual.C w0 * B0) - (Dual.C w0 * A0) * (Dual.C w0 * B1)) -
             Dual.C m1 * ((Dual.C w0 * A2) * (Dual.C w0 * B0) - (Dual.C w0 * A0) * (Dual.C w0 * B2)) +
             Dual.C m0 * ((Dual.C w0 * A2) * (Dual.C w0 * B1) - (Dual.C w0 * A1) * (Dual.C w0 * B2)))).eps =
          w0 ^ 2 * (Dual.C (1 / 16 : K5) *
            (Dual.C m2 * (A1 * B0 - A0 * B1) -
             Dual.C m1 * (A2 * B0 - A0 * B2) +
             Dual.C m0 * (A2 * B1 - A1 * B2))).eps := by
        intro m2 m1 m0 A2 A1 A0 B2 B1 B0
        simp only [Dual.C_val, Dual.C_eps, Dual.add_val, Dual.add_eps, Dual.sub_val, Dual.sub_eps,
          Dual.mul_val, Dual.mul_eps]
        ring
      have hsub : ∀ x y z : Dual K5, Dual.C w0 * x - Dual.C w0 * y - Dual.C w0 * z = Dual.C w0 * (x - y - z) :=
        fun x y z => by ring
      have hsub1 : ∀ x y z : Dual K5, Dual.C w0 * x - Dual.C w0 * y - Dual.C w0 * z + ⟨0, (10 / 7 : K5) * b * w0⟩ =
          Dual.C w0 * (x - y - z + ⟨0, (10 / 7 : K5) * b⟩) := by
        intro x y z; ext <;> simp only [Dual.C_val, Dual.C_eps, Dual.add_val, Dual.add_eps, Dual.sub_val, Dual.sub_eps,
          Dual.mul_val, Dual.mul_eps] <;> ring
      dsimp only [numM_D, numM_12_of]
      rw [hdHS, hdHS, hdHS, hdHQ, hdHQ, hdHQ, hdHQ, hsub, hsub1]
      have hC_rhs : ∀ (m2 m1 m0 : K5) (d10 d20 d21 : Dual K5),
          (Dual.C (1 / 16 : K5) * (Dual.C m2 * d10 - Dual.C m1 * d20 + Dual.C m0 * d21)).eps =
          (1 / 16 : K5) * (m2 * d10.eps - m1 * d20.eps + m0 * d21.eps) := by
        intro m2 m1 m0 d10 d20 d21
        simp only [Dual.C_val, Dual.C_eps, Dual.add_eps, Dual.sub_eps, Dual.mul_eps]; ring
      fin_cases mi <;> (simp only [RingHom.id_apply]; rw [hscale, hC_rhs])
    simp only [A0U_D, A0U_12_of, Dual.C_val, Dual.C_eps, Dual.add_eps, Dual.sub_eps, Dual.mul_eps,
      Dual.ofNat_val, Dual.ofNat_eps, RingHom.id_apply, hmi]
    ring
  exact ⟨hM0_L.eq_c (hA0U_D_eq a0 b0), hAY_m2, hAX_m1⟩

private lemma br2_0_q1_lead
    {a_s b_s U V : LaurentSeries K5} {w0 ca0 cb0 c0W0 a0 b0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 / (T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hca0 : ca0 = -(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))
    (hcb0 : cb0 = (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K))
    (hc0W0 : c0W0 = k5Params.c0_V2 * w0 ^ 2)
    (hlin_raw : ca0 * w0 * a0 + cb0 * w0 * b0 + c0W0 = 0)
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead (-1) V w0) :
    let q1_lead0 : K5 → K5 → K5 := fun a b =>
      let qY0 := 9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a +
        (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b +
        (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))
      let cA0 := 9 * ((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a +
        (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b +
        (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K))
      w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 * qY0 + cA0 * EB_of S_K Q_K T_K x_K y_K 0 1)
    HasValGe 0 (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) ∧
    HasValGe 0 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) ∧
    ValLead (-1)
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
       (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V)
      (q1_lead0 a0 b0) ∧
    HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
  have hA := fiveS_sub_9Q_ne; have hB := T_K_sub_3_ne
  set A := 5 * S_K - 9 * Q_K
  set B := T_K - 3
  intro q1_lead0
  have h9_ne : (9 : K5) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hU0 : ValLead 0 U 0 := ValLead.of_hasValGe_succ hU_L.val
  have hu_L : ValLead 0 (u_of U) (-(1 / 9 : K5)) := by
    unfold u_of
    exact ((hU0.sub (ValLead.of_C 1)).div_of_ne (ValLead.of_nat 9) h9_ne).eq_k (by omega) |>.eq_c (by ring)
  have hv_L : ValLead (-1) (v_of V) (w0 / 9) := by
    unfold v_of
    rw [show (V - 1 : LaurentSeries K5) = V + HahnSeries.C (-1 : K5) by
      simp only [map_neg, map_one]; ring]
    exact ((hV_L.add_high (HasValGe.of_C (-1 : K5))).div_of_ne
      (ValLead.of_nat 9) h9_ne).eq_k (by omega)
  have hw09_ne : w0 / 9 ≠ 0 := div_ne_zero hw0_ne h9_ne
  have hneg19_ne : (-(1 / 9 : K5)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero h9_ne)
  have hlinUV {f0 f1 f2 f3 : K5} :
      ValLead (-1) (HahnSeries.C f0 + HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V)
        (f1 * w0) := by
    have ht1 : ValLead (-1) (HahnSeries.C f1 * V) (f1 * w0) :=
      ((ValLead.of_C f1).mul hV_L).eq_k (by omega)
    have hhi : HasValGe 0 (HahnSeries.C f0 + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) :=
      ((HasValGe.of_C f0).add (((HasValGe.of_C f2).mul hU_L.val).mono (by omega))).add
        ((((HasValGe.of_C f3).mul hU_L.val).mul hV_L.val).mono (by omega))
    have hre : HahnSeries.C f0 + HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V =
        HahnSeries.C f1 * V + (HahnSeries.C f0 + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) := by ring
    rw [hre]; exact ht1.add_high hhi
  have hA1_L : ValLead (-1) (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) (A1_of S_K Q_K 0 1 * w0) := by
    have heq : A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C 0 + HahnSeries.C (A1_of S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
        HahnSeries.C (A1_of S_K Q_K 1 1 - A1_of S_K Q_K 0 1) * U * V := by
      simp only [A1_of, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]
      ring
    rw [heq]; exact hlinUV
  have hB1_0 : HasValGe 0 (B1_of (HahnSeries.C T_K) U V) := by
    unfold B1_of
    rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    have hinner : HasValGe (-1) (25 * HahnSeries.C T_K * (5 * HahnSeries.C T_K - 9) ^ 2 -
        4 * (HahnSeries.C T_K - 3) ^ 3 * V) :=
      ((((HasValGe.of_nat 25).mul (HasValGe.of_C T_K)).mul
        ((((HasValGe.of_nat 5).mul (HasValGe.of_C T_K)).sub (HasValGe.of_nat 9)).pow 2)).mono (by omega)).sub
      ((((HasValGe.of_nat 4).mul (((HasValGe.of_C T_K).sub (HasValGe.of_nat 3)).pow 3)).mul hV_L.val).mono (by omega))
    exact (((HasValGe.of_C _).mul hU_L.val).mul hinner).mono (by omega)
  have hEB_L : ValLead (-1) (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (EB_of S_K Q_K T_K x_K y_K 0 1 * w0) := by
    have hbi := EB_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V
    have h00 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0
    have h01 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1
    have h10 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0
    have h11 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV.eq_c (by rw [EB_of_zero_zero, sub_zero])
  have hQY_L (i : Fin 3) : ValLead (-1)
      (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      ((QY_num S_K Q_K T_K x_K y_K 0 1 i - QY_num S_K Q_K T_K x_K y_K 0 0 i) * w0) := by
    have hbi := QY_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have h00 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0 i
    have h01 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1 i
    have h10 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0 i
    have h11 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1 i
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV
  have hQX_L (i : Fin 3) : ValLead (-1)
      (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      ((QX_num S_K Q_K T_K x_K y_K 0 1 i - QX_num S_K Q_K T_K x_K y_K 0 0 i) * w0) := by
    have hbi := QX_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have h00 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0 i
    have h01 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1 i
    have h10 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0 i
    have h11 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1 i
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV
  have hQX_0 : HasValGe 0 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) := by
    have hdot : ValLead (-1) (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s) 0 := by
      have h1 : ValLead (-1) (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s)
          (((QX_num S_K Q_K T_K x_K y_K 0 1 0 - QX_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
            (QX_num S_K Q_K T_K x_K y_K 0 1 1 - QX_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
            (QX_num S_K Q_K T_K x_K y_K 0 1 2 - QX_num S_K Q_K T_K x_K y_K 0 0 2)) * w0) := by
        unfold dot_ab
        exact ((((hQX_L 0).mul ha_L).eq_k (by omega)).add
          (((hQX_L 1).mul hb_L).eq_k (by omega))).add (hQX_L 2) |>.eq_c (by ring)
      refine h1.eq_c ?_
      have hlin0 : B * (-(5 * S_K - 3 * Q_K) * a0 + 6 * S_K * b0) + S_K * A = 0 := by
        have h2581 : (25 / 81 : K5) ≠ 0 := div_ne_zero
          (by exact_mod_cast (by decide : (25 : ℕ) ≠ 0))
          (by exact_mod_cast (by decide : (81 : ℕ) ≠ 0))
        have hw0_mul : B ^ 3 * w0 = -(25 / 4 : K5) * S_K * A ^ 2 := by
          rw [hw0_eq, mul_div_cancel₀ _ (pow_ne_zero 3 hB)]
        apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h2581 hA) (mul_ne_zero (pow_ne_zero 2 hB) hw0_ne))
        rw [mul_zero]
        have hident :
            (25 / 81 : K5) * A * (B ^ 2 * w0) * (B * (-(5 * S_K - 3 * Q_K) * a0 + 6 * S_K * b0) + S_K * A) =
            B ^ 3 * (ca0 * w0 * a0 + cb0 * w0 * b0 + c0W0) +
            (4 / 81 : K5) * B ^ 2 * w0 * (B ^ 3 * w0 + (25 / 4 : K5) * S_K * A ^ 2) := by
          rw [hca0, hcb0, hc0W0]; simp only [CoverParams.c0_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, A, B]
          ring
        rw [hident, hlin_raw, mul_zero, zero_add, hw0_mul]
        ring
      have hprop : B * ((QX_num S_K Q_K T_K x_K y_K 0 1 0 - QX_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
          (QX_num S_K Q_K T_K x_K y_K 0 1 1 - QX_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
          (QX_num S_K Q_K T_K x_K y_K 0 1 2 - QX_num S_K Q_K T_K x_K y_K 0 0 2)) =
          (80 / 81 : K5) * x_K * T_K ^ 2 * S_K ^ 2 * B ^ 3 *
            (23 * S_K ^ 3 - 82 * S_K ^ 2 * Q_K + 71 * S_K * Q_K ^ 2 + 4 * Q_K ^ 3 -
              50 * S_K ^ 2 * x_K + 90 * S_K * Q_K * x_K + 27 * S_K * x_K ^ 2) *
            (B * (-(5 * S_K - 3 * Q_K) * a0 + 6 * S_K * b0) + S_K * A) :=
        QX_num_01_sub_00_factor S_K Q_K T_K x_K y_K a0 b0
      have hzero : (QX_num S_K Q_K T_K x_K y_K 0 1 0 - QX_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
          (QX_num S_K Q_K T_K x_K y_K 0 1 1 - QX_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
          (QX_num S_K Q_K T_K x_K y_K 0 1 2 - QX_num S_K Q_K T_K x_K y_K 0 0 2) = 0 := by
        apply mul_left_cancel₀ hB
        rw [mul_zero, hprop, hlin0, mul_zero]
      rw [hzero, zero_mul]
    exact (hdot.hasValGe_succ.div_of_lead_ne hu_L.val (hu_L.c0.symm ▸ hneg19_ne)).1.mono (by omega)
  have hqY_L : ValLead 0
      (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V)
      (9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
            (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
            (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))) := by
    have hdot : ValLead (-1) (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s)
        (((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
          (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
          (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2)) * w0) := by
      unfold dot_ab
      exact ((((hQY_L 0).mul ha_L).eq_k (by omega)).add
        (((hQY_L 1).mul hb_L).eq_k (by omega))).add (hQY_L 2) |>.eq_c (by ring)
    exact (hdot.div_of_ne hv_L hw09_ne).eq_k (by omega) |>.eq_c (by
      have hdiv (x : K5) : x * w0 / (w0 / 9) = 9 * x := by
        rw [div_div_eq_mul_div, mul_right_comm, mul_div_cancel_right₀ _ hw0_ne, _root_.mul_comm]
      exact hdiv _)
  have hH0_L : ValLead 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) (H0_of S_K Q_K T_K) := by
    rw [show H0_of (HahnSeries.C S_K : LaurentSeries K5) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact ValLead.of_C _
  have hcA1_L : ValLead (-1) (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V)
      (((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a0 +
        (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b0 +
        (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K)) * w0) := by
    have hdA1_L (k : Fin 3) : ValLead (-1) (dA1_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
        (dA1_fn k S_K Q_K 0 1 * w0) := by
      fin_cases k
      · change ValLead (-1) (dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) (dA1_fn 0 S_K Q_K 0 1 * w0)
        have heq : dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
            HahnSeries.C 0 + HahnSeries.C (dA1_fn 0 S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
            HahnSeries.C (dA1_fn 0 S_K Q_K 1 1 - dA1_fn 0 S_K Q_K 0 1) * U * V := by
          simp only [dA1_fn, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]; ring
        rw [heq]; exact hlinUV
      · change ValLead (-1) (dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) (dA1_fn 1 S_K Q_K 0 1 * w0)
        have heq : dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
            HahnSeries.C 0 + HahnSeries.C (dA1_fn 1 S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
            HahnSeries.C (dA1_fn 1 S_K Q_K 1 1 - dA1_fn 1 S_K Q_K 0 1) * U * V := by
          simp only [dA1_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_one, map_zero]; ring
        rw [heq]; exact hlinUV
      · exact (ValLead.of_hasValGe_succ (HasValGe.zero 0)).eq_c (by simp [dA1_fn])
    have hdH0_L (k : Fin 3) : ValLead 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))
        (dH0_fn k S_K Q_K T_K) := by
      rw [show dH0_fn k (HahnSeries.C S_K : LaurentSeries K5) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (dH0_fn k S_K Q_K T_K) by
        fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
      exact ValLead.of_C _
    unfold cA1_of
    exact (((((hH0_L.mul (hdA1_L 0)).sub (hA1_L.mul (hdH0_L 0) |>.eq_k (by omega))).mul ha_L).eq_k (by omega)).add
      ((((hH0_L.mul (hdA1_L 1)).sub (hA1_L.mul (hdH0_L 1) |>.eq_k (by omega))).mul hb_L).eq_k (by omega))).add
      (((hH0_L.mul (hdA1_L 2)).sub (hA1_L.mul (hdH0_L 2) |>.eq_k (by omega))).eq_k (by omega))
      |>.eq_c (by ring)
  have hq1_L : ValLead (-1)
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
       (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V)
      (q1_lead0 a0 b0) := by
    have ht1 := ((hH0_L.mul hA1_L).mul hqY_L).eq_k (k' := -1) (by omega)
    have ht2 : HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)) :=
      ((hH0_L.val.mul hB1_0).mul hQX_0).mono (by omega)
    have ht3 := ((hcA1_L.div_of_ne hv_L hw09_ne).mul hEB_L).eq_k (k' := -1) (by omega)
    have hre : ∀ x y z : LaurentSeries K5, x + y + z = (x + z) + y := fun x y z => by ring
    rw [hre]
    exact ((ht1.add ht3).add_high ht2).eq_c (by
      have hcomb (h a qy ca eb : K5) :
          h * (a * w0) * (9 * qy) + ca * w0 / (w0 / 9) * (eb * w0) =
            w0 * (h * a * (9 * qy) + 9 * ca * eb) := by
        have hdiv : ca * w0 / (w0 / 9) = 9 * ca := by
          rw [div_div_eq_mul_div, mul_right_comm, mul_div_cancel_right₀ _ hw0_ne, _root_.mul_comm]
        rw [hdiv]; ring
      exact hcomb _ _ _ _ _)
  exact ⟨hqY_L.val, hQX_0, hq1_L, hH0_L.val⟩

private lemma br2_0_g_lead_core
    {a_s b_s U V : LaurentSeries K5} {w0 ca0 cb0 c0W0 a0 b0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 / (T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hca0 : ca0 = -(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))
    (hcb0 : cb0 = (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K))
    (hc0W0 : c0W0 = k5Params.c0_V2 * w0 ^ 2)
    (hlin_raw : ca0 * w0 * a0 + cb0 * w0 * b0 + c0W0 = 0)
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead (-1) V w0) :
    let q1_lead0 : K5 → K5 → K5 := fun a b =>
      let qY0 := 9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a +
        (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b +
        (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))
      let cA0 := 9 * ((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a +
        (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b +
        (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K))
      w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 * qY0 + cA0 * EB_of S_K Q_K T_K x_K y_K 0 1)
    ValLead (-3)
      (P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) a_s b_s U V)
      (w0 ^ 2 * A0U_12_of (RingHom.id K5) a0 b0 * q1_lead0 a0 b0) := by
  intro q1_lead0
  obtain ⟨hM0_L, hAY_m2, hAX_m1⟩ := br2_0_numM_bounds hw0_ne ha_L hb_L hU_L hV_L
  obtain ⟨hqY_0, hQX_0, hq1_L, hH0_0⟩ := br2_0_q1_lead hw0_eq hw0_ne hca0 hcb0 hc0W0 hlin_raw ha_L hb_L hU_L hV_L
  have hrest : HasValGe (-2)
      ((A_Y a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
        A_X a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)) *
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2) :=
    (((hAY_m2.mul hqY_0).mono (k2 := -2) (by omega)).add ((hAX_m1.mul hQX_0).mono (k2 := -2) (by omega))).mul
      (hH0_0.pow 2) |>.mono (by omega)
  rw [P18_of_HahnC_eq]
  exact ((hM0_L.mul hq1_L).eq_k (by omega)).add_high hrest

private lemma br2_0_g_lead
    {W2s U V ca cb c0W : LaurentSeries K5} {w0 ca0 cb0 c0W0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 / (T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0) (hcb0_ne : cb0 ≠ 0)
    (hca0 : ca0 = -(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))
    (hcb0 : cb0 = (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K))
    (hc0W0 : c0W0 = k5Params.c0_V2 * w0 ^ 2)
    (hw0_L : ValLead 0 W2s w0) (hU_L : ValLead 1 U 1) (hV_L : ValLead (-1) V w0)
    (hca_L : ValLead 0 ca ca0) (hcb_L : ValLead 0 cb cb0) (hc0W_L : ValLead 0 c0W c0W0) :
    let q1_lead0 : K5 → K5 → K5 := fun a b =>
      let qY0 := 9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a +
        (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b +
        (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))
      let cA0 := 9 * ((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a +
        (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b +
        (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K))
      w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 * qY0 + cA0 * EB_of S_K Q_K T_K x_K y_K 0 1)
    ∀ z : K5,
      let a := z / w0; let b := -(ca0 * z + c0W0) / (w0 * cb0)
      ValLead (-3)
        (P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K)
          (HahnSeries.C z / W2s) (-(ca * HahnSeries.C z + c0W) / (W2s * cb)) U V)
        (w0 ^ 2 * A0U_12_of (RingHom.id K5) a b * q1_lead0 a b) := by
  intro q1_lead0 z
  let a0 : K5 := z / w0
  let b0 : K5 := -(ca0 * z + c0W0) / (w0 * cb0)
  have ha_L : ValLead 0 (HahnSeries.C z / W2s) a0 := ((ValLead.of_C z).div_of_ne hw0_L hw0_ne).eq_k (by omega)
  have hb_L : ValLead 0 (-(ca * HahnSeries.C z + c0W) / (W2s * cb)) b0 := by
    have hnum : ValLead 0 (-(ca * HahnSeries.C z + c0W)) (-(ca0 * z + c0W0)) :=
      (((hca_L.mul (ValLead.of_C z)).eq_k (by omega)).add hc0W_L).neg
    have hden : ValLead 0 (W2s * cb) (w0 * cb0) := (hw0_L.mul hcb_L).eq_k (by omega)
    exact (hnum.div_of_ne hden (mul_ne_zero hw0_ne hcb0_ne)).eq_k (by omega)
  have hlin_raw : ca0 * w0 * a0 + cb0 * w0 * b0 + c0W0 = 0 := by
    dsimp only [a0, b0]; field_simp [hw0_ne, hcb0_ne]; ring
  exact br2_0_g_lead_core hw0_eq hw0_ne hca0 hcb0 hc0W0 hlin_raw ha_L hb_L hU_L hV_L


end SymmetricSexticResidual.LocalResidueU0

open scoped LaurentSeries in
theorem solution :
    (∀ (mi : Fin 10) (a b : SymmetricSexticResidual.K5Field.K5),
      SymmetricSexticResidual.LocalResidueU0.numM_12_of (RingHom.id SymmetricSexticResidual.K5Field.K5) mi a b =
        (8 * (SymmetricSexticResidual.SheetCalculus.numM mi a b
                (SymmetricSexticResidual.K5Field.S_K - a * SymmetricSexticResidual.K5Field.T_K)
                (SymmetricSexticResidual.K5Field.Q_K - b * SymmetricSexticResidual.K5Field.T_K) 1 1 -
              SymmetricSexticResidual.SheetCalculus.numM mi a b
                (SymmetricSexticResidual.K5Field.S_K - a * SymmetricSexticResidual.K5Field.T_K)
                (SymmetricSexticResidual.K5Field.Q_K - b * SymmetricSexticResidual.K5Field.T_K) (-1) 1) -
          (SymmetricSexticResidual.SheetCalculus.numM mi a b
                (SymmetricSexticResidual.K5Field.S_K - a * SymmetricSexticResidual.K5Field.T_K)
                (SymmetricSexticResidual.K5Field.Q_K - b * SymmetricSexticResidual.K5Field.T_K) 2 1 -
           SymmetricSexticResidual.SheetCalculus.numM mi a b
                (SymmetricSexticResidual.K5Field.S_K - a * SymmetricSexticResidual.K5Field.T_K)
                (SymmetricSexticResidual.K5Field.Q_K - b * SymmetricSexticResidual.K5Field.T_K) (-2) 1)) / 12) ∧
    (∀ {W2s U V ca cb c0W : LaurentSeries SymmetricSexticResidual.K5Field.K5}
      {w0 ca0 cb0 c0W0 : SymmetricSexticResidual.K5Field.K5},
      w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 /
        (SymmetricSexticResidual.K5Field.T_K - 3) ^ 3 →
      w0 ≠ 0 → cb0 ≠ 0 →
      ca0 = -(25 / 81 : SymmetricSexticResidual.K5Field.K5) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) →
      cb0 = (50 / 27 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) →
      c0W0 = SymmetricSexticResidual.CoverAlgebra.k5Params.c0_V2 * w0 ^ 2 →
      QuadraticCovers.ValLead 0 W2s w0 →
      QuadraticCovers.ValLead 1 U 1 →
      QuadraticCovers.ValLead (-1) V w0 →
      QuadraticCovers.ValLead 0 ca ca0 →
      QuadraticCovers.ValLead 0 cb cb0 →
      QuadraticCovers.ValLead 0 c0W c0W0 →
      let q1_lead0 : SymmetricSexticResidual.K5Field.K5 →
          SymmetricSexticResidual.K5Field.K5 → SymmetricSexticResidual.K5Field.K5 := fun a b =>
        let qY0 := 9 * ((SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 1 0 -
          SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 0 0) * a +
          (SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 1 1 -
          SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 0 1) * b +
          (SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 1 2 -
          SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 0 2))
        let cA0 := 9 * ((SymmetricSexticResidual.SheetCalculus.H0_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K *
          SymmetricSexticResidual.SheetCalculus.dA1_fn 0
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 -
          SymmetricSexticResidual.SheetCalculus.A1_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 *
          SymmetricSexticResidual.SheetCalculus.dH0_fn 0
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K) * a +
          (SymmetricSexticResidual.SheetCalculus.H0_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K *
          SymmetricSexticResidual.SheetCalculus.dA1_fn 1
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 -
          SymmetricSexticResidual.SheetCalculus.A1_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 *
          SymmetricSexticResidual.SheetCalculus.dH0_fn 1
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K) * b +
          (SymmetricSexticResidual.SheetCalculus.H0_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K *
          SymmetricSexticResidual.SheetCalculus.dA1_fn 2
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 -
          SymmetricSexticResidual.SheetCalculus.A1_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 *
          SymmetricSexticResidual.SheetCalculus.dH0_fn 2
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K))
        w0 * (SymmetricSexticResidual.SheetCalculus.H0_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K *
          SymmetricSexticResidual.SheetCalculus.A1_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 * qY0 +
          cA0 * SymmetricSexticResidual.SheetCalculus.EB_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 1)
      ∀ z : SymmetricSexticResidual.K5Field.K5,
        let a := z / w0; let b := -(ca0 * z + c0W0) / (w0 * cb0)
        QuadraticCovers.ValLead (-3)
          (SymmetricSexticResidual.SheetCalculus.P18_of
            (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
            (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
            (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
            (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
            (HahnSeries.C SymmetricSexticResidual.K5Field.y_K)
            (HahnSeries.C z / W2s) (-(ca * HahnSeries.C z + c0W) / (W2s * cb)) U V)
          (w0 ^ 2 * SymmetricSexticResidual.LocalResidueU0.A0U_12_of
            (RingHom.id SymmetricSexticResidual.K5Field.K5) a b * q1_lead0 a b)) :=
  And.intro
    SymmetricSexticResidual.LocalResidueU0.numM_12_of_eq_interp
    @SymmetricSexticResidual.LocalResidueU0.br2_0_g_lead
