-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.infinityCoefficient_eta
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:53:12.697231+00:00
-- url     : https://prove2.me/submissions/e09ae66a-9ed9-48ca-9de3-d014ba7fe031

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
import Definitions.Def_HodgeComputerSSR_RInfData
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_lead3_alg
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_weights_and_jets
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br2_vanishes
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_g_valLead
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_p4_valDual
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_combine_K5

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open Polynomial
open scoped LaurentSeries PowerSeries
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.VerticalIdentity
  SymmetricSexticResidual.LocalResidueU0 SymmetricSexticResidual.LocalResidueInfAlg
  QuadraticCovers
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

private abbrev A0V_U3_poly := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_lead3_alg.A0V_U3_poly
private abbrev W1_inf_valDual := HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_and_jets.W1_valDual
private abbrev W1_inf_weights := HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_and_jets.W1_weights

lemma br1_inf_eta_AC_coeff_one : (br1_inf eta_AC).coeff 1 = -toK5_RInf / L_K ^ 2 := by
  let U := HahnSeries.single (-1 : ℤ) (1 : K5)
  let V := W1_inf / U
  let ca := evalInvT k5Params.ca_h
  let cb := evalInvT k5Params.cb_h
  let c0W := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.c0W)
  let d2_2 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_2)
  let d2_1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_1)
  let d2_0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_0)
  let d1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d1_z)
  let d0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d0_z)
  let res := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)
  let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (z / W1_inf) (-(ca * z + c0W) / (W1_inf * cb)) U V
  let p := interp4 g
  let P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
  let P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
  have hbr : br1_inf eta_AC =
      (-(P1 * d0 - P0 * d1) * U ^ 3 * W1_inf * cb ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res) :=
    branchHom_eta_AC_of_eq ψinf ψinf_C W1_inf W1_inf_eq_ψinf U ψinf_X evalInvT (RingHom.ext ψinf_toRat)
      V ca cb c0W d2_2 d2_1 d2_0 d1 d0 res g p P1 P0
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [hbr]
  let pref := -(U ^ 3 * W1_inf * cb ^ 4) /
    (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res)
  let A4 := pref * ((-d2_1 ^ 3 + 2 * d2_2 * d2_1 * d2_0) * d0 - (-d2_1 ^ 2 * d2_0 + d2_2 * d2_0 ^ 2) * d1)
  let A3 := pref * ((d2_2 * (d2_1 ^ 2 - d2_2 * d2_0)) * d0 - (d2_2 * d2_1 * d2_0) * d1)
  let A2 := pref * ((-d2_2 ^ 2 * d2_1) * d0 - (-d2_2 ^ 2 * d2_0) * d1)
  let A1 := pref * (d2_2 ^ 3 * d0)
  let A0 := pref * (-d2_2 ^ 3 * d1)
  have hsplit : -(P1 * d0 - P0 * d1) * U ^ 3 * W1_inf * cb ^ 4 /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res) =
      A4 * p.1 + A3 * p.2.1 + A2 * p.2.2.1 + A1 * p.2.2.2.1 + A0 * p.2.2.2.2 := by
    have hP := P1_d0_sub_P0_d1_split d2_2 d2_1 d2_0 d1 d0 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
    dsimp only [A4, A3, A2, A1, A0, pref, P1, P0]
    rw [hP]; ring
  rw [hsplit]
  obtain ⟨hA4_D, hA3_L, hA2_L, hA1_5, hA0_5, _, _⟩ := W1_inf_weights
  set S3Q := S_K - 3 * Q_K; set T59 := 5 * T_K - 9
  have hS3Q' := S_K_sub_3Q_ne
  have hS3Q : S3Q ≠ 0 := S_K_sub_3Q_ne; have hT := T_K_ne_zero; have hT59 : T59 ≠ 0 := fiveT_sub_9_ne; have hL : L_K ≠ 0 := L_K_ne_zero
  set w0 : K5 := -(k5Params.Cv0 / k5Params.Bv2)
  set w1 : K5 := k5Params.Cv0 * k5Params.Bv1 / k5Params.Bv2 ^ 2
  have hw0_eq : w0 = -(25 / 4 : K5) * T_K * T59 ^ 2 / S3Q ^ 3 := by
    dsimp only [w0]; simp only [CoverParams.Cv0, CoverParams.Bv2, CoverParams.inv243, k5Params_inv3,
      k5Params_S, k5Params_Q, k5Params_T, S3Q, T59]; field_simp [hS3Q']
  have hw1_eq : w1 = w0 * ((243 / 4 : K5) * k5Params.Bv1 / S3Q ^ 3) := by
    dsimp only [w1, w0]; simp only [CoverParams.Bv2, CoverParams.inv243, k5Params_inv3,
      k5Params_S, k5Params_Q, S3Q]; field_simp [hS3Q']; ring
  have hw0_ne : w0 ≠ 0 := neg_ne_zero.mpr (div_ne_zero k5Params_Cv0_ne k5Params_Bv2_ne)
  have hW_D : ValDual 0 W1_inf ⟨w0, w1⟩ := W1_inf_valDual
  have hU_D : ValDual (-1) U (Dual.C 1) := ValDual.of_single (-1) 1
  have hV_D : ValDual 1 V ⟨w0, w1⟩ := (hW_D.div_of_ne hU_D one_ne_zero).eq_k (by omega) |>.eq_d (by
    ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.invOfNe, Dual.C_val, Dual.C_eps] <;> ring)
  have hca_D : ValDual (-2) ca ⟨-(4 / 81 : K5) * S3Q ^ 2,
      (143 / 81 : K5) * S_K ^ 2 - (184 / 27) * S_K * Q_K + (52 / 9) * Q_K ^ 2⟩ :=
    (ValDual.of_evalInvT _ deg2_ca (by omega)).eq_d (by
      ext <;> (simp only [CoverParams.ca_h, coeff_quadU, CoverParams.inv9, CoverParams.inv27,
        CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q, S3Q]; ring))
  have hcb_D : ValDual (-2) cb ⟨(4 / 27 : K5) * S3Q ^ 2,
      -(92 / 27 : K5) * S_K ^ 2 + (104 / 9) * S_K * Q_K - (22 / 3) * Q_K ^ 2 + (10 / 7) * Q_K + (10 / 7)⟩ :=
    (ValDual.of_evalInvT _ deg2_cb (by omega)).eq_d (by
      ext <;> (simp only [CoverParams.cb_h, coeff_quadU, CoverParams.inv9, CoverParams.inv27,
        k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, S3Q]; ring))
  have hc0W_L : ValLead (-2) c0W (-(25 / 81 : K5) * T59 * (5 * T_K - 3)) :=
    (evalInvT_toUW_valLead_W1 _ _ _).eq_c (by
      simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T, T59]; ring)
  -- `ValLead (-3)` for `g (C z)` -> `p3[-3], p2[-3]` and `HasValGe (-3)` for `p1, p0`!
  set q1_1 : K5 := evalBivK5 q1_m1_u1_biv / 107163
  set q1_0 : K5 := evalBivK5 q1_m1_u0_biv / (3 * T_K * T59 * 107163)
  set g0 : K5 → K5 := fun z =>
    (w0 * A0V_Uk 3 (z / w0) (z / w0 / 3 + -S3Q * (5 * T_K - 3) / (3 * T_K * T59))
      (S_K - z / w0 * T_K) (Q_K - (z / w0 / 3 + -S3Q * (5 * T_K - 3) / (3 * T_K * T59)) * T_K)) *
    (q1_1 * (z / w0) + q1_0)
  have hg_L := HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_g_valLead hw0_eq hw0_ne hW_D.toValLead hU_D.toValLead hV_D.toValLead
    hca_D.toValLead hcb_D.toValLead hc0W_L
  obtain ⟨_, hp3_L, hp2_L, hp1_L, hp0_L⟩ := ValLead.interp4_of (g := g) (g0 := g0) hg_L
  -- `ValDual (-3)` for `p4`:
  have hp4_D := HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_p4_valDual hw0_eq hw1_eq hw0_ne hW_D hU_D hV_D hca_D hcb_D hc0W_L
  -- Compute `(interp4 g0).2.1` (`p3[-3]`) and `(interp4 g0).2.2.1` (`p2[-3]`) via `A0V_U3_poly`!
  set c3_A : K5 := (73 / 7971615 : K5) * T59 * S3Q ^ 2
  set c2_A : K5 := A32_2_q_fn S_K Q_K T_K * T59 * S3Q / (14849347275 * (3 * T_K * T59))
  set c1_A : K5 := A32_1_q_fn S_K Q_K T_K * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2)
  have hp32_eq :
      (interp4 g0).2.1 = w0⁻¹ ^ 2 * (c3_A * q1_0 + c2_A * q1_1) ∧
      (interp4 g0).2.2.1 = w0⁻¹ * (c2_A * q1_0 + c1_A * q1_1) := by
    have hpoly (z : K5) :
        A0V_Uk 3 (z / w0) (z / w0 / 3 + -S3Q * (5 * T_K - 3) / (3 * T_K * T59))
          (S_K - z / w0 * T_K) (Q_K - (z / w0 / 3 + -S3Q * (5 * T_K - 3) / (3 * T_K * T59)) * T_K) =
        c3_A * (z / w0) ^ 3 + c2_A * (z / w0) ^ 2 + c1_A * (z / w0) +
        A0V_Uk 3 0 (-S3Q * (5 * T_K - 3) / (3 * T_K * T59)) S_K (Q_K - (-S3Q * (5 * T_K - 3) / (3 * T_K * T59)) * T_K) := by
      simpa only [c3_A, c2_A, c1_A, S3Q, T59] using A0V_U3_poly S_K Q_K T_K (z / w0) hT hT59
    dsimp only [g0]; unfold interp4
    simp only [hpoly]
    constructor <;> (field_simp [hw0_ne]; ring)
  -- Read `coeff 1` of `A4 * p4 + A3 * p3 + A2 * p2 + A1 * p1 + A0 * p0`!
  have hT4 : ValDual 0 (A4 * p.1) _ := (hA4_D.mul hp4_D).eq_k (by omega)
  have hT3 : ValLead 1 (A3 * p.2.1) _ := (hA3_L.mul (hp3_L.eq_c hp32_eq.1)).eq_k (by omega)
  have hT2 : ValLead 1 (A2 * p.2.2.1) _ := (hA2_L.mul (hp2_L.eq_c hp32_eq.2)).eq_k (by omega)
  have hT1 : HasValGe 2 (A1 * p.2.2.2.1) := (hA1_5.mul hp1_L.val).mono (by omega)
  have hT0 : HasValGe 2 (A0 * p.2.2.2.2) := (hA0_5.mul hp0_L.val).mono (by omega)
  have htot := ((hT4.add_shift1 (hT3.add hT2)).add_high (hT1.add hT0))
  have hre : A4 * p.1 + A3 * p.2.1 + A2 * p.2.2.1 + A1 * p.2.2.2.1 + A0 * p.2.2.2.2 =
      (A4 * p.1 + (A3 * p.2.1 + A2 * p.2.2.1)) + (A1 * p.2.2.2.1 + A0 * p.2.2.2.2) := by ring
  rw [hre, show (1 : ℤ) = 0 + 1 by norm_num, htot.c1]
  exact HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_combine_K5 hw0_eq hS3Q hT59 hL

/-! ### Section 6: Main Theorem `infinityCoefficient_eta` -/

theorem infinityCoefficient_eta :
    CrossedRationalResidue.infinityCoefficient CoverResidue.eta = -toK5_RInf / L_K ^ 2 := by
  rw [infinityCoefficient_eq_coeff_one]
  unfold CoverResidue.eta
  rw [map_trace_AC_eq_sum_branches ψinf W1_inf W2_inf W1_inf_eq_ψinf W2_inf_eq_ψinf W1_W2_inf_sum_ψinf,
    HahnSeries.coeff_add]
  change (br1_inf eta_AC).coeff 1 + (br2_inf eta_AC).coeff 1 = _
  rw [br1_inf_eta_AC_coeff_one, HodgeComputer.SymmetricSexticResidual.Proof.localInf_br2_vanishes, add_zero]

end SymmetricSexticResidual.LocalResidueInf

theorem solution :
    CrossedRationalResidue.infinityCoefficient SymmetricSexticResidual.CoverResidue.eta =
      -SymmetricSexticResidual.LocalResidueU0.toK5_RInf /
        SymmetricSexticResidual.LocalResidueU0.L_K ^ 2 :=
  SymmetricSexticResidual.LocalResidueInf.infinityCoefficient_eta
