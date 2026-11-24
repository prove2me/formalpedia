-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_q1_valDual
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T21:03:24.273287+00:00
-- url     : https://prove2.me/submissions/bf46bd15-ce89-498a-981e-8308ac3d6dc0

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_branch_jet_helpers
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_sheet_splits
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_biv_bridges

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open Polynomial
open scoped LaurentSeries PowerSeries
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.VerticalIdentity SymmetricSexticResidual.LocalResidueU0
  SymmetricSexticResidual.LocalResidueInfAlg QuadraticCovers
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

private abbrev EB_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.EB_bilinear
private abbrev QY_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QY_bilinear
private abbrev QX_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QX_bilinear
private abbrev A0V_ValLead_of := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.A0V_ValLead
private abbrev QY_10_u1_zero := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.2.2.2.2.2.2.2.2
private abbrev ringEval_H0_7_inf := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.1
private abbrev ringEval_dH0_7_inf := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.1
private abbrev evalBivK5_QY10 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.1
private abbrev evalBivK5_QX10 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.1
private abbrev evalBivK5_QY00 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.1
private abbrev evalBivK5_QX00 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.1
private abbrev evalBivK5_QY11 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.2.1
private abbrev evalBivK5_QX11 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.2.2.1
private abbrev evalBivK5_EB10 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.2.2.2.1
private abbrev evalBivK5_EB11 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.2.2.2.2.1

private lemma br1_inf_hbi_D {U V : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (a00 a01 a10 a11 : K5) :
    ValDual (-1) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V)
      ⟨a10, a00 + a11 * w0⟩ := by
  have hre : HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V =
      (HahnSeries.C a10 * U + (HahnSeries.C a00 + HahnSeries.C a11 * (U * V))) + HahnSeries.C a01 * V := by ring
  rw [hre]
  have hm : ValDual (-1) (HahnSeries.C a10 * U) (Dual.C a10) :=
    ((ValDual.of_C a10).mul hU_D).eq_k (by omega) |>.eq_d (by rw [← map_mul, mul_one])
  have hs : ValLead 0 (HahnSeries.C a00 + HahnSeries.C a11 * (U * V)) (a00 + a11 * w0) :=
    ((ValLead.of_C a00).add (((ValLead.of_C a11).mul ((hU_D.toValLead.mul hV_D.toValLead).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega))).eq_c (by simp only [Dual.C_val]; ring)
  have hhi : HasValGe 1 (HahnSeries.C a01 * V) := ((HasValGe.of_C a01).mul hV_D.val).mono (by omega)
  exact ((hm.add_shift1 hs).add_high hhi).eq_d (by ext <;> simp)

private lemma br1_inf_EB_valDual {U V : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩) :
    ValDual (-1) (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) ⟨evalBivK5 EB10_biv / 243, evalBivK5 EB11_biv / 243 * w0⟩ := by
  have hbi := EB_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V
  have hmap (u0 v0 : K5) : (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) : LaurentSeries K5) =
      HahnSeries.C (EB_of S_K Q_K T_K x_K y_K u0 v0) := by
    simp only [EB_of, W2_of, DX2_of, DY2_of, dF5_fn, br_fn, LX_of, LY_of,
      dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact (br1_inf_hbi_D hU_D hV_D _ _ _ _).eq_d (by
    have hEB00 : EB_of S_K Q_K T_K x_K y_K 0 0 = 0 := by simp only [EB_of, br_fn, dLX_fn, dLY_fn]; ring
    ext
    · rw [evalBivK5_EB10]; ring
    · rw [evalBivK5_EB11, hEB00]; ring)

private lemma br1_inf_QY_valDual {U V : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩) (i : Fin 3) :
    ValDual (-1)
      (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      ⟨evalBivK5 (QY10_biv i) / 1701, evalBivK5 (QY00_biv i) / 1701 + evalBivK5 (QY11_biv i) / 1701 * w0⟩ := by
  have hbi := QY_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
  have hmap (u0 v0 : K5) : (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
      HahnSeries.C (QY_num S_K Q_K T_K x_K y_K u0 v0 i) := by
    fin_cases i <;> simp only [QY_num, Omega_F, dDX2_F, F_contract, dF5_fn, dH0_fn, dDX2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact (br1_inf_hbi_D hU_D hV_D _ _ _ _).eq_d (by ext <;> rw [evalBivK5_QY10, evalBivK5_QY00, evalBivK5_QY11] <;> ring)

private lemma br1_inf_QX_valDual {U V : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩) (i : Fin 3) :
    ValDual (-1)
      (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      ⟨evalBivK5 (QX10_biv i) / 1701, evalBivK5 (QX00_biv i) / 1701 + evalBivK5 (QX11_biv i) / 1701 * w0⟩ := by
  have hbi := QX_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
  have hmap (u0 v0 : K5) : (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
      HahnSeries.C (QX_num S_K Q_K T_K x_K y_K u0 v0 i) := by
    fin_cases i <;> simp only [QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact (br1_inf_hbi_D hU_D hV_D _ _ _ _).eq_d (by ext <;> rw [evalBivK5_QX10, evalBivK5_QX00, evalBivK5_QX11] <;> ring)


private lemma br1_inf_q1_lead1_valDual {U V aa ab b0s : LaurentSeries K5} {w0 w1 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * T_K * (5 * T_K - 9) ^ 2 / (S_K - 3 * Q_K) ^ 3)
    (hw1_eq : w1 = w0 * ((243 / 4 : K5) * k5Params.Bv1 / (S_K - 3 * Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0)
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (haa_D : ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : ValDual 0 ab (⟨1 / 3, (-(3 / 28 : K5) * (S_K - 3 * Q_K) *
      (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * (S_K - 3 * Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩)) :
    let hqY : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (aa * z) (ab * z + b0s) / v_of V
    let hqX : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (aa * z) (ab * z + b0s) / u_of U
    let hq1 : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * hqY z +
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * B1_of (HahnSeries.C T_K) U V * hqX z +
      (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (aa * z) (ab * z + b0s) U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V
    let S3Q := S_K - 3 * Q_K
    let r1 : K5 := (-(3 / 28 : K5) * S3Q * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * S3Q ^ 3)
    ValDual (-1) (hqY 1 - hqY 0)
      ⟨0, -9 * w0⁻¹ * (r1 * evalBivK5 (QY10_biv 1) / 1701 +
        evalBivK5 cQY_00_biv / 5103 + w0 * evalBivK5 cQY_11_biv / 5103)⟩ ∧
    ValDual 0 (hqX 1 - hqX 0)
      ⟨w0⁻¹ * (evalBivK5 cQX_0_biv / 567),
       w0⁻¹ * ((evalBivK5 cQX_1_biv + 28 * S3Q ^ 3 * evalBivK5 cQX_0_biv) / (28 * 567 * S3Q ^ 3))⟩ ∧
    ValDual (-1) (hq1 1 - hq1 0)
      ⟨w0⁻¹ * (evalBivK5 q1_m1_u1_biv / 107163), w0⁻¹ * (evalBivK5 q1_0_u1_biv / (28 * 107163 * S3Q ^ 3))⟩ := by
  intro hqY hqX hq1 S3Q r1
  set T59 := 5 * T_K - 9
  set rb_sc : K5 := -(3 / 28 : K5) * S3Q * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)
  have hS3Q := S_K_sub_3Q_ne; have hT := T_K_ne_zero; have hT59 := fiveT_sub_9_ne
  have h9_ne : (9 : K5) ≠ 0 := ofNat_ne_zero 9
  have hneg19_ne : (-(1 / 9 : K5)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero h9_ne)
  have h19_ne : (1 / 9 : K5) ≠ 0 := div_ne_zero one_ne_zero h9_ne
  have hu_D : ValDual (-1) (u_of U) ⟨1 / 9, -(1 / 9)⟩ := by
    unfold u_of
    have h1 : ValDual (-1) (U - 1) ⟨1, -1⟩ := by
      have : U - 1 = U + HahnSeries.C (-1 : K5) := by simp [sub_eq_add_neg]
      rw [this]; exact hU_D.add_shift1 (ValLead.of_C (-1)) |>.eq_d (by ext <;> simp)
    refine ((h1.div_of_ne (ValDual.of_ofNat 9) (by simpa only [Dual.C_val] using h9_ne)).eq_k (by omega)).eq_d ?_
    exact (dual_div_eq_iff _ _ _ (by simpa only [Dual.C_val] using h9_ne)).mpr (by
      ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps] <;> ring)
  have hv_D : ValDual 0 (v_of V) ⟨-(1 / 9), w0 / 9⟩ := by
    unfold v_of
    have h1 : ValDual 0 (V - 1) ⟨-1, w0⟩ := by
      have : V - 1 = HahnSeries.C (-1 : K5) + V := by simp [sub_eq_add_neg, add_comm]
      rw [this]; exact (ValDual.of_C (-1 : K5)).add_shift1 hV_D.toValLead |>.eq_d (by ext <;> simp)
    refine ((h1.div_of_ne (ValDual.of_ofNat 9) (by simpa only [Dual.C_val] using h9_ne)).eq_k (by omega)).eq_d ?_
    exact (dual_div_eq_iff _ _ _ (by simpa only [Dual.C_val] using h9_ne)).mpr (by
      ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps] <;> ring)
  have hEB_D := br1_inf_EB_valDual hU_D hV_D
  have hQY_D := br1_inf_QY_valDual hU_D hV_D
  have hQX_D := br1_inf_QX_valDual hU_D hV_D
  have hl1_qY_D : ValDual (-1) (hqY 1 - hqY 0)
      ⟨0, -9 * w0⁻¹ * (r1 * evalBivK5 (QY10_biv 1) / 1701 +
        evalBivK5 cQY_00_biv / 5103 + w0 * evalBivK5 cQY_11_biv / 5103)⟩ := by
    have heq : hqY 1 - hqY 0 = (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V 0 * aa +
        QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V 1 * ab) / v_of V := by
      dsimp only [hqY, dot_ab]; ring
    rw [heq]
    have hnum : ValDual (-1) _ _ := (((hQY_D 0).mul haa_D).eq_k (k' := -1) (by omega)).add (((hQY_D 1).mul hab_D).eq_k (k' := -1) (by omega))
    refine valDual_eq_fd ((hnum.div_of_ne hv_D hneg19_ne).eq_k (k' := -1) (by omega)) (by ring) ?_
    exact (dual_div_eq_iff _ _ _ hneg19_ne).mpr (by
      have hqy0 : 3 * evalBivK5 (QY10_biv 0) + evalBivK5 (QY10_biv 1) = 0 := by
        rw [evalBivK5_QY10, evalBivK5_QY10]; linear_combination 1701 * QY_10_u1_zero S_K Q_K T_K x_K y_K
      ext
      · simp only [Dual.add_val, Dual.mul_val]; linear_combination (w0⁻¹ / 5103) * hqy0
      · simp only [Dual.add_eps, Dual.mul_val, Dual.mul_eps,
          cQY_00_biv, cQY_11_biv, evalBivK5_bivAdd, evalBivK5_bivScale]
        push_cast; linear_combination -(w1 / (5103 * w0 ^ 2)) * hqy0)
  have hl1_qX_D : ValDual 0 (hqX 1 - hqX 0)
      ⟨w0⁻¹ * (evalBivK5 cQX_0_biv / 567),
       w0⁻¹ * ((evalBivK5 cQX_1_biv + 28 * S3Q ^ 3 * evalBivK5 cQX_0_biv) / (28 * 567 * S3Q ^ 3))⟩ := by
    have heq : hqX 1 - hqX 0 = (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V 0 * aa +
        QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V 1 * ab) / u_of U := by
      dsimp only [hqX, dot_ab]; ring
    rw [heq]
    have hnum : ValDual (-1) _ _ := (((hQX_D 0).mul haa_D).eq_k (k' := -1) (by omega)).add (((hQX_D 1).mul hab_D).eq_k (k' := -1) (by omega))
    refine valDual_eq_fd ((hnum.div_of_ne hu_D h19_ne).eq_k (k' := 0) (by omega)) (by ring) ?_
    exact (dual_div_eq_iff _ _ _ h19_ne).mpr (by
      have hBv1_1701 : ringEval vK5 Bv1_1701_exact_e = 1701 * k5Params.Bv1 := by
        simp only [Bv1_1701_exact_e, ringEval, eS, eQ, eT, vK5, CoverParams.Bv1, CoverParams.inv9,
          CoverParams.inv27, CoverParams.inv243, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T]; ring
      ext
      · simp only [Dual.add_val, Dual.mul_val, cQX_0_biv, evalBivK5_bivAdd, evalBivK5_bivScale]; push_cast; ring
      · simp only [Dual.add_eps, Dual.mul_val, Dual.mul_eps,
          cQX_1_biv, cQX_0_biv, cQX_00_biv, cQX_11_biv, evalBivK5_bivAdd, evalBivK5_bivScale,
          evalBivK5_bscE, ringEval, hBv1_1701, rb_sc_28_e, rb_num_28_e, S3Q_e, w0_sc4_e, T59_e, eS, eQ, eT, vK5]
        push_cast; rw [hw1_eq, hw0_eq]; dsimp only [r1, rb_sc, S3Q, T59]
        field_simp [hS3Q, hT, hT59]; ring)
  have hA1_D : ValDual 0 (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
      ⟨(25 / 27 : K5) * T_K * T59 ^ 2,
       -(4 / 27 : K5) * S3Q ^ 3 * w1 + (25 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 * w0⟩ := by
    have hre : A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C (-(4 / 27 : K5) * S3Q ^ 3) * (U * V) +
        HahnSeries.C ((25 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2) * V := by
      simp only [A1_of, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    have hm : ValDual 0 (HahnSeries.C (-(4 / 27 : K5) * S3Q ^ 3) * (U * V))
        ⟨(25 / 27 : K5) * T_K * T59 ^ 2, -(4 / 27 : K5) * S3Q ^ 3 * w1⟩ :=
      ((ValDual.of_C _).mul ((hU_D.mul hV_D).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega) |>.eq_d (by
        ext
        · simp only [Dual.mul_val, Dual.C_val]; rw [hw0_eq]; field_simp [hS3Q]; ring
        · simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps]; ring)
    have hs : ValLead 1 (HahnSeries.C ((25 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2) * V)
        ((25 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 * w0) :=
      ((ValLead.of_C _).mul hV_D.toValLead).eq_k (k' := 1) (by omega)
    exact (hm.add_shift1 hs).eq_d (by ext <;> simp)
  have hB1_D : ValDual (-1) (B1_of (HahnSeries.C T_K) U V)
      ⟨(25 / 27 : K5) * T_K * T59 ^ 2, -(4 / 27 : K5) * (T_K - 3) ^ 3 * w0⟩ := by
    have hre : B1_of (HahnSeries.C T_K) U V =
        HahnSeries.C ((25 / 27 : K5) * T_K * T59 ^ 2) * U +
        HahnSeries.C (-(4 / 27 : K5) * (T_K - 3) ^ 3) * (U * V) := by
      simp only [B1_of, T59, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    have hm : ValDual (-1) (HahnSeries.C ((25 / 27 : K5) * T_K * T59 ^ 2) * U)
        (Dual.C ((25 / 27 : K5) * T_K * T59 ^ 2)) :=
      ((ValDual.of_C _).mul hU_D).eq_k (k' := -1) (by omega) |>.eq_d (by rw [← map_mul, mul_one])
    have hs : ValLead 0 (HahnSeries.C (-(4 / 27 : K5) * (T_K - 3) ^ 3) * (U * V))
        (-(4 / 27 : K5) * (T_K - 3) ^ 3 * w0) :=
      ((ValLead.of_C _).mul ((hU_D.toValLead.mul hV_D.toValLead).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega) |>.eq_c (by simp only [Dual.C_val]; ring)
    exact hm.add_shift1 hs |>.eq_d (by ext <;> simp [Dual.C_val, Dual.C_eps, Dual.pow_eq])
  have hH0_D : ValDual 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))
      (Dual.C (ringEval vK5 H0_int_e / 7)) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact (ValDual.of_C _).eq_d (by congr 1; rw [ringEval_H0_7_inf]; ring)
  have hdA1_0_D : ValDual 0 (dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
      ⟨-(4 / 9 : K5) * S3Q ^ 2 * w0, -(4 / 9 : K5) * S3Q ^ 2 * w1 + (25 / 27 : K5) * (5 * S_K - 9 * Q_K) * (15 * S_K - 9 * Q_K) * w0⟩ := by
    have hre : dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C (-(4 / 9 : K5) * S3Q ^ 2) * (U * V) +
        HahnSeries.C ((25 / 27 : K5) * (5 * S_K - 9 * Q_K) * (15 * S_K - 9 * Q_K)) * V := by
      simp only [dA1_fn, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    exact (((ValDual.of_C _).mul ((hU_D.mul hV_D).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega)).add_shift1
      (((ValLead.of_C _).mul hV_D.toValLead).eq_k (k' := 1) (by omega)) |>.eq_d (by ext <;> simp [Dual.C_val, Dual.C_eps, Dual.pow_eq])
  have hdA1_1_D : ValDual 0 (dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
      ⟨(4 / 3 : K5) * S3Q ^ 2 * w0, (4 / 3 : K5) * S3Q ^ 2 * w1 - (50 / 3 : K5) * S_K * (5 * S_K - 9 * Q_K) * w0⟩ := by
    have hre : dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C ((4 / 3 : K5) * S3Q ^ 2) * (U * V) +
        HahnSeries.C (-(50 / 3 : K5) * S_K * (5 * S_K - 9 * Q_K)) * V := by
      simp only [dA1_fn, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    exact (((ValDual.of_C _).mul ((hU_D.mul hV_D).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega)).add_shift1
      (((ValLead.of_C _).mul hV_D.toValLead).eq_k (k' := 1) (by omega)) |>.eq_d (by ext <;> simp [Dual.C_val, Dual.C_eps, Dual.pow_eq]; ring)
  have hdH0_D (k : Fin 3) : ValDual 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))
      (Dual.C (ringEval vK5 (dH0_7_inf_e k) / 7)) := by
    rw [show dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (dH0_fn k S_K Q_K T_K) by
      fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact (ValDual.of_C _).eq_d (by congr 1; rw [ringEval_dH0_7_inf]; ring)
  have hl1_q1_D : ValDual (-1) (hq1 1 - hq1 0)
      ⟨w0⁻¹ * (evalBivK5 q1_m1_u1_biv / 107163), w0⁻¹ * (evalBivK5 q1_0_u1_biv / (28 * 107163 * S3Q ^ 3))⟩ := by
    have heq : hq1 1 - hq1 0 =
        H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * (hqY 1 - hqY 0) +
        H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * B1_of (HahnSeries.C T_K) U V * (hqX 1 - hqX 0) +
        (((H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
           A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * aa +
          (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
           A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * ab) / v_of V) *
          EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V := by
      dsimp only [hq1, cA1_of]; ring
    rw [heq]
    have ht1 : ValDual (-1) _ _ := ((hH0_D.mul hA1_D).mul hl1_qY_D).eq_k (by omega)
    have ht2 : ValDual (-1) _ _ := ((hH0_D.mul hB1_D).mul hl1_qX_D).eq_k (by omega)
    have hcA1_l1 : ValDual 0 _ _ := ((((hH0_D.mul hdA1_0_D).sub (hA1_D.mul (hdH0_D 0))).mul haa_D).eq_k (by omega)).add
      ((((hH0_D.mul hdA1_1_D).sub (hA1_D.mul (hdH0_D 1))).mul hab_D).eq_k (by omega))
    have ht3 : ValDual (-1) _ _ := ((hcA1_l1.div_of_ne hv_D hneg19_ne).mul hEB_D).eq_k (by omega)
    refine valDual_eq_fd ((ht1.add ht2).add ht3) (by ring) ?_
    ext
    · simp only [Dual.add_val, Dual.mul_val, Dual.sub_val, Dual.C_val, Dual.invOfNe,
        q1_m1_u1_biv, evalBivK5_bscE, evalBivK5_bivAdd, ringEval, T59_e, eT, vK5, dH0_301_21_e, T59]
      field_simp [hw0_ne]; ring
    · have hS3Q_e : ringEval vK5 S3Q_e = S_K - 3 * Q_K := rfl
      have hT59_e : ringEval vK5 T59_e = 5 * T_K - 9 := rfl
      have hA5_e : ringEval vK5 A5_e = 5 * S_K - 9 * Q_K := rfl
      have hrb_num : -(3 / 28 : K5) * (S_K - 3 * Q_K) * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90) =
          (S_K - 3 * Q_K) * ringEval vK5 rb_num_28_e / 28 := by
        simp only [rb_num_28_e, ringEval, eS, eQ, vK5]; ring
      simp only [Dual.add_val, Dual.add_eps, Dual.mul_val, Dual.mul_eps, Dual.sub_val, Dual.sub_eps,
        Dual.C_val, Dual.C_eps, Dual.invOfNe,
        q1_0_u1_biv, evalBivK5_bscE, evalBivK5_bivAdd, evalBivK5_bivSub, ringEval,
        hT59_e, hS3Q_e, hA5_e, w0_sc4_e, rb_sc_28_e, dH0_301_21_e, eS, eQ, eT, vK5]
      rw [hw0_eq]; dsimp only [r1, rb_sc, S3Q, T59]; rw [hrb_num]
      generalize ringEval vK5 rb_num_28_e = vrb
      generalize evalBivK5 (QY10_biv 1) = vQY1; generalize evalBivK5 cQY_00_biv = vQY00; generalize evalBivK5 cQY_11_biv = vQY11
      generalize evalBivK5 cQX_0_biv = vQX0; generalize evalBivK5 cQX_1_biv = vQX1
      generalize evalBivK5 EB10_biv = vEB10; generalize evalBivK5 EB11_biv = vEB11
      generalize ringEval vK5 H0_int_e = vH0; generalize ringEval vK5 (dH0_7_inf_e 0) = vdH0; generalize ringEval vK5 (dH0_7_inf_e 1) = vdH1
      generalize (S_K - 3 * Q_K) = s3q at hS3Q ⊢
      generalize (5 * T_K - 9) = t59 at hT59 ⊢
      field_simp [hS3Q, hT, hT59]; ring
  exact ⟨hl1_qY_D, hl1_qX_D, hl1_q1_D⟩


end SymmetricSexticResidual.LocalResidueInf

open scoped LaurentSeries in
theorem solution
    {U V aa ab b0s : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w0 w1 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)
    (hw1_eq : w1 = w0 * ((243 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.CoverAlgebra.k5Params.Bv1 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0)
    (hU_D : QuadraticCovers.ValDual (-1) U (QuadraticCovers.Dual.C 1))
    (hV_D : QuadraticCovers.ValDual 1 V ⟨w0, w1⟩)
    (haa_D : QuadraticCovers.ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : QuadraticCovers.ValDual 0 ab (⟨1 / 3, (-(3 / 28 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
      (119 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
       560 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
       630 * SymmetricSexticResidual.K5Field.Q_K ^ 2 + 90 * SymmetricSexticResidual.K5Field.Q_K + 90)) /
      (3 * (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩)) :
    let hqY : LaurentSeries SymmetricSexticResidual.K5Field.K5 → LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.dot_ab
        (SymmetricSexticResidual.SheetCalculus.QY_num
          (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.y_K) U V) (aa * z) (ab * z + b0s) /
        SymmetricSexticResidual.SheetCalculus.v_of V
    let hqX : LaurentSeries SymmetricSexticResidual.K5Field.K5 → LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.dot_ab
        (SymmetricSexticResidual.SheetCalculus.QX_num
          (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.y_K) U V) (aa * z) (ab * z + b0s) /
        SymmetricSexticResidual.SheetCalculus.u_of U
    let hq1 : LaurentSeries SymmetricSexticResidual.K5Field.K5 → LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.H0_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K) *
      SymmetricSexticResidual.SheetCalculus.A1_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K) U V * hqY z +
      SymmetricSexticResidual.SheetCalculus.H0_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K) *
      SymmetricSexticResidual.SheetCalculus.B1_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K) U V * hqX z +
      (SymmetricSexticResidual.SheetCalculus.cA1_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K) (aa * z) (ab * z + b0s) U V /
        SymmetricSexticResidual.SheetCalculus.v_of V) *
        SymmetricSexticResidual.SheetCalculus.EB_of
          (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.y_K) U V
    let S3Q := SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K
    let r1 : SymmetricSexticResidual.K5Field.K5 :=
      (-(3 / 28 : SymmetricSexticResidual.K5Field.K5) * S3Q *
        (119 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
         560 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
         630 * SymmetricSexticResidual.K5Field.Q_K ^ 2 + 90 * SymmetricSexticResidual.K5Field.Q_K + 90)) / (3 * S3Q ^ 3)
    QuadraticCovers.ValDual (-1) (hqY 1 - hqY 0)
      ⟨0, -9 * w0⁻¹ * (r1 * SymmetricSexticResidual.LocalResidueU0.evalBivK5
          (SymmetricSexticResidual.LocalResidueInf.QY10_biv 1) / 1701 +
        SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQY_00_biv / 5103 +
        w0 * SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQY_11_biv / 5103)⟩ ∧
    QuadraticCovers.ValDual 0 (hqX 1 - hqX 0)
      ⟨w0⁻¹ * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQX_0_biv / 567),
       w0⁻¹ * ((SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQX_1_biv +
         28 * S3Q ^ 3 * SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQX_0_biv) /
         (28 * 567 * S3Q ^ 3))⟩ ∧
    QuadraticCovers.ValDual (-1) (hq1 1 - hq1 0)
      ⟨w0⁻¹ * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163),
       w0⁻¹ * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_0_u1_biv /
         (28 * 107163 * S3Q ^ 3))⟩ :=
  SymmetricSexticResidual.LocalResidueInf.br1_inf_q1_lead1_valDual hw0_eq hw1_eq hw0_ne hU_D hV_D haa_D hab_D
