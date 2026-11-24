-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_p4_valDual
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T21:40:29.780026+00:00
-- url     : https://prove2.me/submissions/364cb2b0-778b-4503-b96c-b9d932a003f7

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_reg_identities
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_branch_jet_helpers
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_lead3_alg
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_sheet_splits
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_weights_and_jets
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_biv_bridges
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_fV
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_q1_valDual

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

private abbrev numM_isPolyDeg3 := @HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.numM_deg3
private abbrev AX_U3_lead3_at_third := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_lead3_alg.AX_U3_lead3_at_third
private abbrev numM_split_UV := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.1
private abbrev AY_t3_U3_eq_zero := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.1
private abbrev A_X_split_UV := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.2.1
private abbrev numM_Uk_valLead := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_and_jets.numM_Uk_valLead
private abbrev numM_Uk_hasValGe := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_and_jets.numM_Uk_hasValGe
private abbrev ringEval_H0_7_inf := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.1
private abbrev br1_inf_fV_lead3_valDual := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_fV
private abbrev br1_inf_q1_lead1_valDual := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_q1_valDual

private lemma IsPolyDeg_numM {R : Type} [Field R] [CharZero R]
    (S Q T U V aa ab b0 : R) (mi : Fin 10) :
    IsPolyDeg 3 (fun z : R => numM mi (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T) U V) :=
  IsPolyDeg.congr (numM_isPolyDeg3 mi S Q T U V aa 0 ab b0) (fun z => by simp only [add_zero])

private lemma br1_inf_fX_lead3_valLead {U V aa ab b0s : LaurentSeries K5} {w0 w1 : K5}
    (hw0_ne : w0 ≠ 0)
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (haa_D : ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : ValDual 0 ab (⟨1 / 3, (-(3 / 28 : K5) * (S_K - 3 * Q_K) *
      (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * (S_K - 3 * Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩))
    (hb0_L : ValLead 0 b0s (-((S_K - 3 * Q_K) * (5 * T_K - 3)) / (3 * T_K * (5 * T_K - 9)))) :
    let fX : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      A_X (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V *
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2
    ValLead (-2) ((fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6)
      (w0⁻¹ * ((2 / 885735 : K5) * (5 * T_K - 9) * (S_K - 3 * Q_K) ^ 2) * (ringEval vK5 H0_int_e / 7) ^ 2) := by
  intro fX
  set S3Q := S_K - 3 * Q_K; set T59 := 5 * T_K - 9
  have h6_ne : (6 : K5) ≠ 0 := ofNat_ne_zero 6
  have hH0_L : ValLead 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) (ringEval vK5 H0_int_e / 7) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact (ValLead.of_C _).eq_c (by rw [ringEval_H0_7_inf]; ring)
  let leadAX (k : Fin 4) : LaurentSeries K5 :=
    let f := fun z : LaurentSeries K5 => AX_Uk k (aa * z) (ab * z + b0s)
      (HahnSeries.C S_K - aa * z * HahnSeries.C T_K) (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6
  have hX_split : (fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6 =
      (U * V ^ 2 * (U ^ 3 * leadAX 3) + U * V ^ 2 * (U ^ 2 * leadAX 2 + U * leadAX 1 + leadAX 0)) *
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2 := by
    dsimp only [fX, leadAX]; simp only [A_X_split_UV]; ring
  rw [hX_split]
  have hAXk0 (k : Fin 4) (z0 : K5) : ValLead 0
      (AX_Uk k (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K))
      (AX_Uk k (w0⁻¹ * z0) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)))
        (S_K - w0⁻¹ * z0 * T_K) (Q_K - ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) * T_K)) := by
    have haL : ValLead 0 (aa * HahnSeries.C z0) (w0⁻¹ * z0) := (haa_D.toValLead.mul (ValLead.of_C z0)).eq_k (by omega)
    have hbL : ValLead 0 (ab * HahnSeries.C z0 + b0s) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) :=
      (((hab_D.toValLead.mul (ValLead.of_C z0)).eq_k (by omega)).add hb0_L).eq_c (by simp only [Dual.mul_val]; ring)
    have hξSL : ValLead 0 (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K) (S_K - w0⁻¹ * z0 * T_K) :=
      (ValLead.of_C S_K).sub ((haL.mul (ValLead.of_C T_K)).eq_k (by omega))
    have hξQL : ValLead 0 (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K)
        (Q_K - ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) * T_K) :=
      (ValLead.of_C Q_K).sub ((hbL.mul (ValLead.of_C T_K)).eq_k (by omega))
    have hC (r : K5) {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
        ValLead 0 (HahnSeries.C r * f) (r * v) := ((ValLead.of_C r).mul hf).eq_k (by omega)
    have hN (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
        ValLead 0 ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) ((no_index (OfNat.ofNat n) : K5) * v) :=
      ((ValLead.of_ofNat n).mul hf).eq_k (by omega)
    have hnum (mi : Fin 10) : ValLead 0 (numM_Uk k mi (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
          (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K))
        (numM_Uk k mi (w0⁻¹ * z0) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)))
          (S_K - w0⁻¹ * z0 * T_K) (Q_K - ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) * T_K)) :=
      numM_Uk_valLead k mi haL hbL hξSL hξQL
    have hp (i j : Fin 10) := (hN 5 (hnum i)).sub (hN 9 (hnum j))
    unfold AX_Uk
    simpa only [map_div₀, map_neg, map_ofNat] using
      ((hC (-(8 / 405 : K5)) (hp 3 4)).sub (hC (476 / 7185 : K5) (hp 7 8))).add (hC (6916 / 35925 : K5) (hp 8 9))
  have hL3 : ValLead (-2) (U * V ^ 2 * (U ^ 3 * leadAX 3)) (w0⁻¹ * ((2 / 885735 : K5) * T59 * S3Q ^ 2)) := by
    have hf2 := hAXk0 3 2; have hf1 := hAXk0 3 1; have hf0 := hAXk0 3 0; have hfm1 := hAXk0 3 (-1)
    have hcomb := ((((hf2.sub (((ValLead.of_ofNat 3).mul hf1).eq_k (k' := 0) (by omega))).add
      (((ValLead.of_ofNat 3).mul hf0).eq_k (k' := 0) (by omega))).sub hfm1).div_of_ne
      (ValLead.of_ofNat 6) h6_ne).eq_k (k' := 0) (by omega)
    have hU3 : ValLead (-3) (U ^ 3) 1 := (hU_D.toValLead.pow 3).eq_k (by omega) |>.eq_c (by simp)
    refine valLead_eq_fc (((hU_D.toValLead.mul (hV_D.toValLead.pow 2)).mul (hU3.mul hcomb)).eq_k (k' := -2) (by omega))
      (by dsimp only [leadAX]; simp only [map_ofNat, map_one, map_zero, map_neg]) ?_
    have h3 := AX_U3_lead3_at_third S_K Q_K T_K w0⁻¹ (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
    dsimp only at h3
    have h4 : ((AX_Uk 3 (w0⁻¹ * 2) (w0⁻¹ / 3 * 2 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 2 * T_K) (Q_K - (w0⁻¹ / 3 * 2 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) -
        (3 : K5) * AX_Uk 3 (w0⁻¹ * 1) (w0⁻¹ / 3 * 1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 1 * T_K) (Q_K - (w0⁻¹ / 3 * 1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) +
        (3 : K5) * AX_Uk 3 (w0⁻¹ * 0) (w0⁻¹ / 3 * 0 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 0 * T_K) (Q_K - (w0⁻¹ / 3 * 0 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) -
        AX_Uk 3 (w0⁻¹ * -1) (w0⁻¹ / 3 * -1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * -1 * T_K) (Q_K - (w0⁻¹ / 3 * -1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K)) / (6 : K5)) =
        w0⁻¹ ^ 3 * ((2 / 885735 : K5) * T59 * S3Q ^ 2) := by
      simpa only [S3Q, T59] using h3
    push_cast; simp only [Dual.C_val, one_mul, h4]; field_simp [hw0_ne]
  have hhiX : HasValGe (-1) (U * V ^ 2 * (U ^ 2 * leadAX 2 + U * leadAX 1 + leadAX 0)) := by
    have h0 (k : Fin 4) : HasValGe 0 (leadAX k) := by
      have hf2 := (hAXk0 k 2).val; have hf1 := (hAXk0 k 1).val; have hf0 := (hAXk0 k 0).val; have hfm1 := (hAXk0 k (-1)).val
      exact hasValGe_eq_f (((((hf2.sub (((HasValGe.of_ofNat 3).mul hf1).mono (k2 := 0) (by omega))).add
        (((HasValGe.of_ofNat 3).mul hf0).mono (k2 := 0) (by omega))).sub hfm1).div_of_lead_ne
        (HasValGe.of_ofNat 6) (by rw [(ValLead.of_ofNat 6).c0]; exact h6_ne)).1.mono (k2 := 0) (by omega))
        (by dsimp only [leadAX]; simp only [map_ofNat, map_one, map_zero, map_neg])
    exact ((hU_D.val.mul (hV_D.val.pow 2)).mul
      (((((hU_D.val.pow 2).mul (h0 2)).mono (k2 := -2) (by omega)).add
        ((hU_D.val.mul (h0 1)).mono (k2 := -2) (by omega))).add ((h0 0).mono (k2 := -2) (by omega)))).mono (by omega)
  exact valLead_eq_fc (((hL3.add_high hhiX).mul (hH0_L.pow 2)).eq_k (k' := -2) (by omega)) rfl
    (by dsimp only [S3Q, T59])

private lemma br1_inf_fUfY_lead3_ge {U V aa ab b0s : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (haa_val : HasValGe 0 aa) (hab_val : HasValGe 0 ab) (hb0_val : HasValGe 0 b0s) :
    let fU : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      A_0U (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V / U
    let fY : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      A_Y (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V *
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2
    HasValGe 0 ((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) ∧
    HasValGe (-1) ((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) := by
  intro fU fY
  have hH0_0 : HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact HasValGe.of_C _
  have hnum_at (z0 : K5) (mi : Fin 10) :
      HasValGe (-1) (numM mi (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K) U V) := by
    rw [numM_split_UV]
    have ha0 : HasValGe 0 (aa * HahnSeries.C z0) := (haa_val.mul (HasValGe.of_C z0)).mono (by omega)
    have hb0' : HasValGe 0 (ab * HahnSeries.C z0 + b0s) :=
      ((hab_val.mul (HasValGe.of_C z0)).mono (by omega)).add hb0_val
    have hξS0 : HasValGe 0 (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K) :=
      (HasValGe.of_C S_K).sub ((ha0.mul (HasValGe.of_C T_K)).mono (by omega))
    have hξQ0 : HasValGe 0 (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K) :=
      (HasValGe.of_C Q_K).sub ((hb0'.mul (HasValGe.of_C T_K)).mono (by omega))
    have hUk (k : Fin 4) : HasValGe 0 (numM_Uk k mi (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K)) :=
      numM_Uk_hasValGe k mi ha0 hb0' hξS0 hξQ0
    exact ((hV_D.val.pow 2).mul (((((hU_D.val.pow 3).mul (hUk 3)).mono (k2 := -3) (by omega)).add
      (((hU_D.val.pow 2).mul (hUk 2)).mono (k2 := -3) (by omega))).add
      ((hU_D.val.mul (hUk 1)).mono (k2 := -3) (by omega)) |>.add ((hUk 0).mono (k2 := -3) (by omega)))).mono (by omega)
  have h6_ne : (6 : K5) ≠ 0 := ofNat_ne_zero 6
  have hlead3_ge {f : LaurentSeries K5 → LaurentSeries K5} {k : ℤ}
      (hf : ∀ z0 : K5, HasValGe k (f (HahnSeries.C z0))) :
      HasValGe k ((f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6) := by
    have h2 := hf 2; have h1 := hf 1; have h0 := hf 0; have hm1 := hf (-1)
    exact hasValGe_eq_f (((((h2.sub (((HasValGe.of_ofNat 3).mul h1).mono (k2 := k) (by omega))).add
      (((HasValGe.of_ofNat 3).mul h0).mono (k2 := k) (by omega))).sub hm1).div_of_lead_ne
      (HasValGe.of_ofNat 6) (by rw [(ValLead.of_ofNat 6).c0]; exact h6_ne)).1.mono (k2 := k) (by omega))
      (by simp only [map_ofNat, map_one, map_zero, map_neg])
  constructor
  · apply hlead3_ge; intro z0
    have hm1 := hnum_at z0
    have hsc1 (r : K5) {f : LaurentSeries K5} (hf : HasValGe (-1) f) := ((HasValGe.of_C r).mul hf).mono (k2 := -1) (by omega)
    have hnat1 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} (hf : HasValGe (-1) f) :
        HasValGe (-1) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) := ((HasValGe.of_ofNat n).mul hf).mono (k2 := -1) (by omega)
    have hp1 (i j : Fin 10) := (hnat1 5 (hm1 i)).sub (hnat1 9 (hm1 j))
    have hA0U : HasValGe (-1) (A_0U (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K) U V) := by
      unfold A_0U; simpa only [map_div₀, map_neg, map_ofNat] using
        (((hsc1 (-(19708 / 1257375 : K5)) (hp1 0 1)).add (hsc1 (1472 / 1257375 : K5) (hp1 1 2))).sub
          (hsc1 (16 / 729 : K5) (hp1 3 5))).add (hsc1 (188 / 2025 : K5) (hp1 4 6))
    exact hasValGe_eq_f ((hA0U.div_of_lead_ne hU_D.val (by rw [hU_D.c0]; exact one_ne_zero)).1.mono (k2 := 0) (by omega))
      (by simp only [fU])
  · apply hlead3_ge; intro z0
    have hm1 := hnum_at z0
    have hsc1 (r : K5) {f : LaurentSeries K5} (hf : HasValGe (-1) f) := ((HasValGe.of_C r).mul hf).mono (k2 := -1) (by omega)
    have hnat1 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} (hf : HasValGe (-1) f) :
        HasValGe (-1) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) := ((HasValGe.of_ofNat n).mul hf).mono (k2 := -1) (by omega)
    have hp1 (i j : Fin 10) := (hnat1 5 (hm1 i)).sub (hnat1 9 (hm1 j))
    have hAY : HasValGe (-1) (A_Y (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K) U V) := by
      unfold A_Y
      refine HasValGe.add (HasValGe.add ?_ ?_) ?_
      · simpa only [map_div₀, map_neg, map_ofNat] using
          hsc1 (-(100 / 243 : K5)) ((((hnat1 25 (hm1 3)).sub (hnat1 45 (hm1 4))).sub (hnat1 45 (hm1 5))).add (hnat1 81 (hm1 6)))
      · refine (hV_D.val.mul (?_ : HasValGe (-1) _)).mono (by omega)
        simpa only [map_div₀, map_neg, map_ofNat] using
          (((hsc1 (-(907876 / 33949125 : K5)) (hp1 0 1)).add (hsc1 (2258324 / 33949125 : K5) (hp1 1 2))).add
            (hsc1 (8 / 243 : K5) (hp1 3 5))).sub (hsc1 (64 / 675 : K5) (hp1 4 6))
      · refine ((hU_D.val.mul hV_D.val).mul (?_ : HasValGe (-1) _)).mono (by omega)
        simpa only [map_div₀, map_neg, map_ofNat] using
          (hsc1 (-(123236 / 24249375 : K5)) ((((hm1 0).add (hsc1 (2790 / 77 : K5) (hm1 6))).add (hnat1 28 (hm1 8))).sub
            (hsc1 (5904 / 77 : K5) (hm1 9)))).add
          (hsc1 (492944 / 33949125 : K5) ((((hm1 1).add (hsc1 (927 / 77 : K5) (hm1 6))).add (hsc1 (49 / 5 : K5) (hm1 8))).sub
            (hsc1 (21159 / 770 : K5) (hm1 9))))
    exact hasValGe_eq_f ((hAY.mul (hH0_0.pow 2)).mono (k2 := -1) (by omega)) (by simp only [fY])

-- Standalone Branch 1 (`W1_inf`) `ValDual (-3)` for `p4 = (interp4 g).1` using `interp4_p4_mul`!
private lemma br1_inf_p4_valDual {W1s U V ca cb c0W : LaurentSeries K5} {w0 w1 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * T_K * (5 * T_K - 9) ^ 2 / (S_K - 3 * Q_K) ^ 3)
    (hw1_eq : w1 = w0 * ((243 / 4 : K5) * k5Params.Bv1 / (S_K - 3 * Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0)
    (hW_D : ValDual 0 W1s ⟨w0, w1⟩) (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (hca_D : ValDual (-2) ca ⟨-(4 / 81 : K5) * (S_K - 3 * Q_K) ^ 2,
      (143 / 81 : K5) * S_K ^ 2 - (184 / 27) * S_K * Q_K + (52 / 9) * Q_K ^ 2⟩)
    (hcb_D : ValDual (-2) cb ⟨(4 / 27 : K5) * (S_K - 3 * Q_K) ^ 2,
      -(92 / 27 : K5) * S_K ^ 2 + (104 / 9) * S_K * Q_K - (22 / 3) * Q_K ^ 2 + (10 / 7) * Q_K + (10 / 7)⟩)
    (hc0W_L : ValLead (-2) c0W (-(25 / 81 : K5) * (5 * T_K - 9) * (5 * T_K - 3))) :
    let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) (z / W1s) (-(ca * z + c0W) / (W1s * cb)) U V
    let S3Q := S_K - 3 * Q_K; let T59 := 5 * T_K - 9
    let p4_m3 : K5 := w0⁻¹ ^ 3 * ((73 / 7971615 : K5) * T59 * S3Q ^ 2) * (evalBivK5 q1_m1_u1_biv / 107163)
    let p4_m2 : K5 :=
      w0⁻¹ ^ 3 * ((73 / 7971615 : K5) * T59 * S3Q ^ 2) * (evalBivK5 q1_0_u1_biv / (28 * 107163 * S3Q ^ 3)) +
      w0⁻¹ ^ 3 * (M01_q_fn S_K Q_K T_K * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (evalBivK5 q1_m1_u1_biv / 107163) +
      w0⁻¹ ^ 2 * ((2 / 885735 : K5) * T59 * S3Q ^ 2) * (evalBivK5 cQX_0_biv / 567) * (ringEval vK5 H0_int_e / 7) ^ 2
    ValDual (-3) (interp4 g).1 ⟨p4_m3, p4_m2⟩ := by
  intro g S3Q T59 p4_m3 p4_m2
  have hS3Q := S_K_sub_3Q_ne; have hT := T_K_ne_zero; have hT59 := fiveT_sub_9_ne
  have hcb_ne : (4 / 27 : K5) * S3Q ^ 2 ≠ 0 :=
    mul_ne_zero (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 27)) (pow_ne_zero 2 hS3Q)
  have hW_ne : W1s ≠ 0 := fun h0 => hw0_ne (by have h := hW_D.c0; rw [h0, HahnSeries.coeff_zero] at h; exact h.symm)
  have hcb_s_ne : cb ≠ 0 := fun h0 => hcb_ne (by have h := hcb_D.c0; rw [h0, HahnSeries.coeff_zero] at h; exact h.symm)
  set aa : LaurentSeries K5 := 1 / W1s
  set rca : LaurentSeries K5 := -ca / cb
  set ab : LaurentSeries K5 := rca / W1s
  set b0s : LaurentSeries K5 := -c0W / (W1s * cb)
  have ha_eq (z : LaurentSeries K5) : z / W1s = aa * z := by dsimp only [aa]; ring
  have hb_eq (z : LaurentSeries K5) : -(ca * z + c0W) / (W1s * cb) = ab * z + b0s := by
    dsimp only [ab, rca, b0s]; field_simp [hW_ne, hcb_s_ne]; ring
  set fV : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    A_0V (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
      (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V / V
  set fU : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    A_0U (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
      (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V / U
  set fX : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    A_X (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
      (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V *
    H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2
  set fY : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    A_Y (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
      (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V *
    H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2
  set hqY : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (aa * z) (ab * z + b0s) / v_of V
  set hqX : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (aa * z) (ab * z + b0s) / u_of U
  set hq1 : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * hqY z +
    H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * B1_of (HahnSeries.C T_K) U V * hqX z +
    (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (aa * z) (ab * z + b0s) U V / v_of V) *
      EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V
  have hg_eq : g = fun z => (fV z * hq1 z + fU z * hq1 z) + (fX z * hqX z + fY z * hqY z) := by
    funext z; dsimp only [g, fV, fU, fX, fY, hq1, hqX, hqY]
    rw [P18_of_HahnC_eq, ha_eq z, hb_eq z]; ring
  have hdeg3_m := IsPolyDeg_numM (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) U V aa ab b0s
  have hpair3 (i j : Fin 10) : IsPolyDeg 3 (fun z =>
      5 * numM i (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
            (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V -
      9 * numM j (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
            (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V) :=
    IsPolyDeg.sub (IsPolyDeg.smul_left 5 (hdeg3_m i)) (IsPolyDeg.smul_left 9 (hdeg3_m j))
  have hdeg3_fV : IsPolyDeg 3 fV :=
    IsPolyDeg.div_const (IsPolyDeg.add (IsPolyDeg.sub (IsPolyDeg.add
      (IsPolyDeg.smul_left _ (hpair3 3 4)) (IsPolyDeg.smul_left _ (hpair3 5 6)))
      (IsPolyDeg.smul_left _ (hpair3 7 8))) (IsPolyDeg.smul_left _ (hpair3 8 9))) V
  have hdeg3_fU : IsPolyDeg 3 fU :=
    IsPolyDeg.div_const (IsPolyDeg.add (IsPolyDeg.sub (IsPolyDeg.add
      (IsPolyDeg.smul_left _ (hpair3 0 1)) (IsPolyDeg.smul_left _ (hpair3 1 2)))
      (IsPolyDeg.smul_left _ (hpair3 3 5))) (IsPolyDeg.smul_left _ (hpair3 4 6))) U
  have hdeg3_fX : IsPolyDeg 3 fX :=
    IsPolyDeg.smul_right (IsPolyDeg.smul_left U (IsPolyDeg.add (IsPolyDeg.sub
      (IsPolyDeg.smul_left _ (hpair3 3 4)) (IsPolyDeg.smul_left _ (hpair3 7 8)))
      (IsPolyDeg.smul_left _ (hpair3 8 9)))) _
  have hdeg3_fY : IsPolyDeg 3 fY := by
    unfold fY A_Y
    refine IsPolyDeg.smul_right (IsPolyDeg.add (IsPolyDeg.add ?_ ?_) ?_) _
    · exact IsPolyDeg.smul_left _
        (IsPolyDeg.add (IsPolyDeg.sub (IsPolyDeg.sub
          (IsPolyDeg.smul_left _ (hdeg3_m 3)) (IsPolyDeg.smul_left _ (hdeg3_m 4)))
          (IsPolyDeg.smul_left _ (hdeg3_m 5))) (IsPolyDeg.smul_left _ (hdeg3_m 6)))
    · exact IsPolyDeg.smul_left V (IsPolyDeg.sub (IsPolyDeg.add (IsPolyDeg.add
        (IsPolyDeg.smul_left _ (hpair3 0 1)) (IsPolyDeg.smul_left _ (hpair3 1 2)))
        (IsPolyDeg.smul_left _ (hpair3 3 5))) (IsPolyDeg.smul_left _ (hpair3 4 6)))
    · exact IsPolyDeg.smul_left (U * V) (IsPolyDeg.add
        (IsPolyDeg.smul_left _ (IsPolyDeg.sub (IsPolyDeg.add (IsPolyDeg.add (hdeg3_m 0)
          (IsPolyDeg.smul_left _ (hdeg3_m 6))) (IsPolyDeg.smul_left _ (hdeg3_m 8)))
          (IsPolyDeg.smul_left _ (hdeg3_m 9))))
        (IsPolyDeg.smul_left _ (IsPolyDeg.sub (IsPolyDeg.add (IsPolyDeg.add (hdeg3_m 1)
          (IsPolyDeg.smul_left _ (hdeg3_m 6))) (IsPolyDeg.smul_left _ (hdeg3_m 8)))
          (IsPolyDeg.smul_left _ (hdeg3_m 9)))))
  have hdot1 (f3 : Fin 3 → LaurentSeries K5) : IsPolyDeg 1 (fun z => dot_ab f3 (aa * z) (ab * z + b0s)) :=
    IsPolyDeg.congr (IsPolyDeg.linear (f3 0 * aa + f3 1 * ab) (f3 1 * b0s + f3 2))
      (fun z => by dsimp only [dot_ab]; ring)
  have hdeg1_hqY : IsPolyDeg 1 hqY := IsPolyDeg.div_const (hdot1 _) (v_of V)
  have hdeg1_hqX : IsPolyDeg 1 hqX := IsPolyDeg.div_const (hdot1 _) (u_of U)
  have hdeg1_hq1 : IsPolyDeg 1 hq1 := by
    have hcA1 : IsPolyDeg 1 (fun z => cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (aa * z) (ab * z + b0s) U V) :=
      IsPolyDeg.congr (IsPolyDeg.linear
        ((H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
          A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * aa +
         (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
          A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * ab)
        ((H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
          A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * b0s +
         (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 2 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
          A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 2 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))))
        (fun z => by dsimp only [cA1_of]; ring)
    exact IsPolyDeg.add (IsPolyDeg.add (IsPolyDeg.smul_left _ hdeg1_hqY) (IsPolyDeg.smul_left _ hdeg1_hqX))
      (IsPolyDeg.smul_right (IsPolyDeg.div_const hcA1 _) _)
  have hp4_split : (interp4 g).1 =
      ((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6) * (hq1 1 - hq1 0) +
      ((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) * (hq1 1 - hq1 0) +
      ((fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6) * (hqX 1 - hqX 0) +
      ((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) * (hqY 1 - hqY 0) := by
    rw [hg_eq, interp4_add_p4, interp4_add_p4, interp4_add_p4,
      interp4_p4_mul hdeg3_fV hdeg1_hq1, interp4_p4_mul hdeg3_fU hdeg1_hq1,
      interp4_p4_mul hdeg3_fX hdeg1_hqX, interp4_p4_mul hdeg3_fY hdeg1_hqY]
    ring
  rw [hp4_split]
  set rb_sc : K5 := -(3 / 28 : K5) * S3Q * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)
  set r1 : K5 := rb_sc / (3 * S3Q ^ 3)
  have hrca_D : ValDual 0 rca ⟨1 / 3, r1⟩ := by
    refine ((hca_D.neg.div_of_ne hcb_D hcb_ne).eq_k (by omega)).eq_d ?_
    have hr1_cb : r1 * ((4 / 27 : K5) * (S_K - 3 * Q_K) ^ 2) =
        -(1 / 189 : K5) * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90) := by
      dsimp only [r1, rb_sc, S3Q]; field_simp [hS3Q]; ring
    exact (dual_div_eq_iff _ _ _ hcb_ne).mpr (by
      ext
      · simp only [Dual.neg_val, Dual.mul_val]; ring
      · simp only [Dual.neg_eps, Dual.mul_eps]; rw [_root_.mul_comm _ r1, hr1_cb]; ring)
  have haa_D : ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩ := by
    have hinv := (hW_D.inv_of_ne hw0_ne).eq_k (k' := 0) (by omega)
    simpa only [aa, one_div] using hinv.eq_d (by ext <;> simp [Dual.invOfNe])
  have hab_eq : ab = rca * aa := by dsimp only [ab, aa]; ring
  have hab_D : ValDual 0 ab (⟨1 / 3, r1⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩) := by
    rw [hab_eq]; exact (hrca_D.mul haa_D).eq_k (by omega)
  have hb0_L : ValLead 0 b0s (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) := by
    refine ((hc0W_L.neg.div_of_ne ((hW_D.toValLead.mul hcb_D.toValLead).eq_k (k' := -2) (by omega))
      (mul_ne_zero hw0_ne hcb_ne)).eq_k (by omega)).eq_c ?_
    rw [hw0_eq]; dsimp only [S3Q, T59]; field_simp [hS3Q, hT, hT59]; ring
  have hfV_L3_D := br1_inf_fV_lead3_valDual hw1_eq hw0_ne hab_eq hU_D hV_D hrca_D haa_D hab_D hb0_L
  obtain ⟨hl1_qY_D, hl1_qX_D, hl1_q1_D⟩ := br1_inf_q1_lead1_valDual (b0s := b0s) hw0_eq hw1_eq hw0_ne hU_D hV_D haa_D hab_D
  have hfX_L3_L := br1_inf_fX_lead3_valLead hw0_ne hU_D hV_D haa_D hab_D hb0_L
  obtain ⟨hfU_L3, hfY_L3⟩ := br1_inf_fUfY_lead3_ge hU_D hV_D haa_D.val hab_D.val hb0_L.val
  have hT_V : ValDual (-3) _ _ := (hfV_L3_D.mul hl1_q1_D).eq_k (by omega)
  have hT_U : HasValGe (-1) (((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) * (hq1 1 - hq1 0)) :=
    (hfU_L3.mul hl1_q1_D.val).mono (by omega)
  have hT_X : ValLead (-2) _ _ := (hfX_L3_L.mul hl1_qX_D.toValLead).eq_k (by omega)
  have hT_Y : HasValGe (-1) (((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) * (hqY 1 - hqY 0)) :=
    (hfY_L3.mul (hl1_qY_D.val.inc hl1_qY_D.c0)).mono (by omega)
  have hre :
      ((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6) * (hq1 1 - hq1 0) +
      ((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) * (hq1 1 - hq1 0) +
      ((fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6) * (hqX 1 - hqX 0) +
      ((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) * (hqY 1 - hqY 0) =
      (((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6) * (hq1 1 - hq1 0) +
       ((fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6) * (hqX 1 - hqX 0)) +
      (((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) * (hq1 1 - hq1 0) +
       ((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) * (hqY 1 - hqY 0)) := by ring
  rw [hre]
  exact ((hT_V.add_shift1 hT_X).add_high (hT_U.add hT_Y)).eq_d (by
    ext <;> (simp only [Dual.add_val, Dual.add_eps, Dual.mul_val, Dual.mul_eps, p4_m3, p4_m2, S3Q, T59]; ring))


end SymmetricSexticResidual.LocalResidueInf

open scoped LaurentSeries in
theorem solution
    {W1s U V ca cb c0W : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w0 w1 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.T_K *
      (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)
    (hw1_eq : w1 = w0 * ((243 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.CoverAlgebra.k5Params.Bv1 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0)
    (hW_D : QuadraticCovers.ValDual 0 W1s ⟨w0, w1⟩)
    (hU_D : QuadraticCovers.ValDual (-1) U (QuadraticCovers.Dual.C 1))
    (hV_D : QuadraticCovers.ValDual 1 V ⟨w0, w1⟩)
    (hca_D : QuadraticCovers.ValDual (-2) ca
      ⟨-(4 / 81 : SymmetricSexticResidual.K5Field.K5) *
        (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 2,
       (143 / 81 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 2 -
        (184 / 27) * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
        (52 / 9) * SymmetricSexticResidual.K5Field.Q_K ^ 2⟩)
    (hcb_D : QuadraticCovers.ValDual (-2) cb
      ⟨(4 / 27 : SymmetricSexticResidual.K5Field.K5) *
        (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 2,
       -(92 / 27 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 2 +
        (104 / 9) * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K -
        (22 / 3) * SymmetricSexticResidual.K5Field.Q_K ^ 2 +
        (10 / 7) * SymmetricSexticResidual.K5Field.Q_K + (10 / 7)⟩)
    (hc0W_L : QuadraticCovers.ValLead (-2) c0W
      (-(25 / 81 : SymmetricSexticResidual.K5Field.K5) *
        (5 * SymmetricSexticResidual.K5Field.T_K - 9) *
        (5 * SymmetricSexticResidual.K5Field.T_K - 3))) :
    let g : LaurentSeries SymmetricSexticResidual.K5Field.K5 →
        LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.P18_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.y_K)
        (z / W1s) (-(ca * z + c0W) / (W1s * cb)) U V
    let S3Q := SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K
    let T59 := 5 * SymmetricSexticResidual.K5Field.T_K - 9
    let p4_m3 : SymmetricSexticResidual.K5Field.K5 :=
      w0⁻¹ ^ 3 * ((73 / 7971615 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2) *
      (SymmetricSexticResidual.LocalResidueU0.evalBivK5
        SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163)
    let p4_m2 : SymmetricSexticResidual.K5Field.K5 :=
      w0⁻¹ ^ 3 * ((73 / 7971615 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2) *
        (SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.q1_0_u1_biv / (28 * 107163 * S3Q ^ 3)) +
      w0⁻¹ ^ 3 * (SymmetricSexticResidual.LocalResidueInfAlg.M01_q_fn
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (267288250950 * S3Q ^ 3)) *
        (SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163) +
      w0⁻¹ ^ 2 * ((2 / 885735 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2) *
        (SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.cQX_0_biv / 567) *
        (PolynomialEncoding.SignedExpressions.ringEval
          SymmetricSexticResidual.LocalResidueU0.vK5
          SymmetricSexticResidual.VerticalIdentity.H0_int_e / 7) ^ 2
    QuadraticCovers.ValDual (-3) (QuadraticCovers.interp4 g).1 ⟨p4_m3, p4_m2⟩ :=
  SymmetricSexticResidual.LocalResidueInf.br1_inf_p4_valDual hw0_eq hw1_eq hw0_ne hW_D hU_D hV_D hca_D hcb_D hc0W_L
