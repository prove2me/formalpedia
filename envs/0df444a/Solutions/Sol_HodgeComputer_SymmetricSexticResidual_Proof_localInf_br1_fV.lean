-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_fV
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T20:06:19.084107+00:00
-- url     : https://prove2.me/submissions/48ff58a3-f77d-4a6f-9de0-be8c4e0511ca

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_lead3_alg
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_sheet_splits
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_weights_and_jets

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open Polynomial
open scoped LaurentSeries PowerSeries
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueU0 SymmetricSexticResidual.LocalResidueInfAlg
  QuadraticCovers

private abbrev A0V_U3_lead3_eq := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_lead3_alg.A0V_U3_lead3_eq
private abbrev A0V_U2_lead3_at_third := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_lead3_alg.A0V_U2_lead3_at_third
private abbrev M01_dual_combine := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_lead3_alg.M01_dual_combine
private abbrev A0V_U3_lead3_dual := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_lead3_alg.A0V_U3_lead3_dual
private abbrev A_0V_split_UV := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.1
private abbrev numM_Uk_valLead := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_and_jets.numM_Uk_valLead

private lemma br1_inf_fV_lead3_valDual {U V aa rca ab b0s : LaurentSeries K5} {w0 w1 : K5}
    (hw1_eq : w1 = w0 * ((243 / 4 : K5) * k5Params.Bv1 / (S_K - 3 * Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0) (hab_eq : ab = rca * aa)
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (hrca_D : ValDual 0 rca ⟨1 / 3, (-(3 / 28 : K5) * (S_K - 3 * Q_K) *
      (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * (S_K - 3 * Q_K) ^ 3)⟩)
    (haa_D : ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : ValDual 0 ab (⟨1 / 3, (-(3 / 28 : K5) * (S_K - 3 * Q_K) *
      (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * (S_K - 3 * Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩))
    (hb0_L : ValLead 0 b0s (-((S_K - 3 * Q_K) * (5 * T_K - 3)) / (3 * T_K * (5 * T_K - 9)))) :
    let fV : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      A_0V (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V / V
    let S3Q := S_K - 3 * Q_K; let T59 := 5 * T_K - 9
    ValDual (-2) ((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6)
      ⟨w0⁻¹ ^ 2 * ((73 / 7971615 : K5) * T59 * S3Q ^ 2),
       w0⁻¹ ^ 2 * (M01_q_fn S_K Q_K T_K * T59 * S3Q / (267288250950 * S3Q ^ 3))⟩ := by
  intro fV S3Q T59
  have hS3Q := S_K_sub_3Q_ne
  set rb_sc : K5 := -(3 / 28 : K5) * S3Q * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)
  set r1 : K5 := rb_sc / (3 * S3Q ^ 3)
  have hV_ne : V ≠ 0 := fun h0 => hw0_ne (by have h := hV_D.c0; rw [h0, HahnSeries.coeff_zero] at h; exact h.symm)
  let leadA0V (k : Fin 4) : LaurentSeries K5 :=
    let f := fun z : LaurentSeries K5 => A0V_Uk k (aa * z) (ab * z + b0s)
      (HahnSeries.C S_K - aa * z * HahnSeries.C T_K) (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6
  have hfV_eq : (fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6 =
      V * U ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) aa ab +
      V * U ^ 2 * leadA0V 2 + V * (U * leadA0V 1 + leadA0V 0) := by
    have hsp (z : LaurentSeries K5) : fV z =
        V * (U ^ 3 * A0V_Uk 3 (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) +
        U ^ 2 * A0V_Uk 2 (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) +
        U * A0V_Uk 1 (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) +
        A0V_Uk 0 (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K)) := by
      dsimp only [fV]; rw [A_0V_split_UV]; field_simp [hV_ne]
    dsimp only [leadA0V]
    rw [hsp 2, hsp 1, hsp 0, hsp (-1),
      ← A0V_U3_lead3_eq (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) aa ab b0s]
    ring
  rw [hfV_eq]
  have hhom3 : A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) aa ab =
      aa ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca := by
    rw [hab_eq]; simp only [A0V_U3_lead3_fn]; ring
  have hD1 : ValDual (-2) (V * U ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) aa ab)
      (⟨w0, w1⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩ ^ 3 *
       ⟨(73 / 7971615 : K5) * T59 * S3Q ^ 2,
        -(2 / 2121335325 : K5) * T59 * (-464630 * S_K + 1568725 * Q_K + 34020 * T_K - 23814) * (-S_K + 3 * Q_K) * r1⟩) := by
    rw [hhom3]
    have hpoly : ValDual 0 (A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca)
        ⟨(73 / 7971615 : K5) * T59 * S3Q ^ 2,
         -(2 / 2121335325 : K5) * T59 * (-464630 * S_K + 1568725 * Q_K + 34020 * T_K - 23814) * (-S_K + 3 * Q_K) * r1⟩ := by
      set c0_p : K5 := -7728665 * Q_K ^ 2 - 1746360 * Q_K * T_K + 6563302 * Q_K + 5340850
      set c1_p : K5 := 15457330 * S_K * Q_K + 21962150 * Q_K ^ 2 + 1746360 * S_K * T_K + 10001880 * Q_K * T_K -
        6563302 * S_K - 39046416 * Q_K - 1020600 * T_K - 42108180
      set c2_p : K5 := -7728665 * S_K ^ 2 - 43924300 * S_K * Q_K - 10001880 * S_K * T_K - 14288400 * Q_K * T_K +
        39046416 * S_K + 58069530 * Q_K + 6123600 * T_K + 108446130
      set c3_p : K5 := 21962150 * S_K ^ 2 + 14288400 * S_K * T_K - 58069530 * S_K - 9185400 * T_K - 90567720
      have hre : A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca =
          HahnSeries.C (-(1 / 4949782425 : K5) * T59) *
            (HahnSeries.C c0_p + HahnSeries.C c1_p * rca + HahnSeries.C c2_p * rca ^ 2 + HahnSeries.C c3_p * rca ^ 3) := by
        simp only [A0V_U3_lead3_fn, c0_p, c1_p, c2_p, c3_p, T59,
          map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_one]; ring
      rw [hre]
      have hsum := (((ValDual.of_C c0_p).add (((ValDual.of_C c1_p).mul hrca_D).eq_k (k' := 0) (by omega))).add
        (((ValDual.of_C c2_p).mul (hrca_D.pow 2)).eq_k (k' := 0) (by omega))).add
        (((ValDual.of_C c3_p).mul (hrca_D.pow 3)).eq_k (k' := 0) (by omega))
      refine (((ValDual.of_C (-(1 / 4949782425 : K5) * T59)).mul hsum).eq_k (k' := 0) (by omega)).eq_d ?_
      obtain ⟨hv, he⟩ := A0V_U3_lead3_dual S_K Q_K T_K r1
      ext
      · simp only [Dual.mul_val, Dual.add_val, Dual.C_val, Dual.pow_eq, c0_p, c1_p, c2_p, c3_p]; linear_combination hv
      · simp only [Dual.mul_val, Dual.mul_eps, Dual.add_val, Dual.add_eps, Dual.C_val, Dual.C_eps,
          Dual.pow_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, c0_p, c1_p, c2_p, c3_p]; linear_combination he
    have hU3 : ValDual (-3) (U ^ 3) (Dual.C 1) := (hU_D.pow 3).eq_k (by omega) |>.eq_d (by rw [← map_pow, one_pow])
    have hre2 : V * U ^ 3 * (aa ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca) =
        (V * aa ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca) * U ^ 3 := by ring
    rw [hre2]
    exact ((((hV_D.mul (haa_D.pow 3)).mul hpoly).eq_k (k' := 1) (by omega)).mul hU3).eq_k (k' := -2) (by omega) |>.eq_d
      (by rw [map_one, mul_one])
  have hUk0 (k : Fin 4) (z0 : K5) : ValLead 0
      (A0V_Uk k (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K))
      (A0V_Uk k (w0⁻¹ * z0) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)))
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
    unfold A0V_Uk
    simpa only [map_div₀, map_neg, map_ofNat] using
      (((hC (-(892 / 3645 : K5)) (hp 3 4)).add (hC (40 / 81 : K5) (hp 5 6))).sub
        (hC (112 / 2395 : K5) (hp 7 8))).add (hC (392 / 11975 : K5) (hp 8 9))
  have h6_ne : (6 : K5) ≠ 0 := ofNat_ne_zero 6
  have hL2 : ValLead (-1) (V * U ^ 2 * leadA0V 2)
      (w0⁻¹ ^ 2 * ((1 / 53457650190 : K5) * T59 *
        (-50137409 * S_K ^ 2 + 300824454 * S_K * Q_K - 451236681 * Q_K ^ 2 - 10001880 * S_K * T_K +
         30005640 * Q_K * T_K - 45873099 * S_K + 137619297 * Q_K - 10103940 * T_K + 58998753))) := by
    have hf2 := hUk0 2 2; have hf1 := hUk0 2 1; have hf0 := hUk0 2 0; have hfm1 := hUk0 2 (-1)
    have hcomb := ((((hf2.sub (((ValLead.of_ofNat 3).mul hf1).eq_k (k' := 0) (by omega))).add
      (((ValLead.of_ofNat 3).mul hf0).eq_k (k' := 0) (by omega))).sub hfm1).div_of_ne
      (ValLead.of_ofNat 6) h6_ne).eq_k (k' := 0) (by omega)
    have hU2 : ValLead (-2) (U ^ 2) 1 := (hU_D.toValLead.pow 2).eq_k (by omega) |>.eq_c (by simp)
    refine valLead_eq_fc (((hV_D.toValLead.mul hU2).mul hcomb).eq_k (k' := -1) (by omega))
      (by dsimp only [leadA0V]; simp only [map_ofNat, map_one, map_zero, map_neg]) ?_
    have h3 := A0V_U2_lead3_at_third S_K Q_K T_K w0⁻¹ (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
    dsimp only at h3
    have h4 : ((A0V_Uk 2 (w0⁻¹ * 2) (w0⁻¹ / 3 * 2 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 2 * T_K) (Q_K - (w0⁻¹ / 3 * 2 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) -
        (3 : K5) * A0V_Uk 2 (w0⁻¹ * 1) (w0⁻¹ / 3 * 1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 1 * T_K) (Q_K - (w0⁻¹ / 3 * 1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) +
        (3 : K5) * A0V_Uk 2 (w0⁻¹ * 0) (w0⁻¹ / 3 * 0 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 0 * T_K) (Q_K - (w0⁻¹ / 3 * 0 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) -
        A0V_Uk 2 (w0⁻¹ * -1) (w0⁻¹ / 3 * -1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * -1 * T_K) (Q_K - (w0⁻¹ / 3 * -1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K)) / (6 : K5)) =
        w0⁻¹ ^ 3 * ((1 / 53457650190 : K5) * T59 *
          (-50137409 * S_K ^ 2 + 300824454 * S_K * Q_K - 451236681 * Q_K ^ 2 - 10001880 * S_K * T_K +
           30005640 * Q_K * T_K - 45873099 * S_K + 137619297 * Q_K - 10103940 * T_K + 58998753)) := by
      simpa only [T59] using h3
    push_cast; rw [mul_one, h4]; field_simp [hw0_ne]
  have hhi0 : HasValGe 0 (V * (U * leadA0V 1 + leadA0V 0)) := by
    have h0 (k : Fin 4) : HasValGe 0 (leadA0V k) := by
      have hf2 := (hUk0 k 2).val; have hf1 := (hUk0 k 1).val; have hf0 := (hUk0 k 0).val; have hfm1 := (hUk0 k (-1)).val
      exact hasValGe_eq_f (((((hf2.sub (((HasValGe.of_ofNat 3).mul hf1).mono (k2 := 0) (by omega))).add
        (((HasValGe.of_ofNat 3).mul hf0).mono (k2 := 0) (by omega))).sub hfm1).div_of_lead_ne
        (HasValGe.of_ofNat 6) (by rw [(ValLead.of_ofNat 6).c0]; exact h6_ne)).1.mono (k2 := 0) (by omega))
        (by dsimp only [leadA0V]; simp only [map_ofNat, map_one, map_zero, map_neg])
    exact (hV_D.val.mul (((hU_D.val.mul (h0 1)).mono (k2 := -1) (by omega)).add ((h0 0).mono (k2 := -1) (by omega)))).mono (by omega)
  refine ((hD1.add_shift1 hL2).add_high hhi0).eq_d ?_
  have hcomb := M01_dual_combine S_K Q_K T_K
  have hBv1_eq : k5Params.Bv1 = (143 / 243 : K5) * S_K ^ 3 - (92 / 27) * S_K ^ 2 * Q_K + (52 / 9) * S_K * Q_K ^ 2 -
      (22 / 9) * Q_K ^ 3 + (143 / 243) * T_K ^ 3 - (92 / 27) * T_K ^ 2 + (52 / 9) * T_K - (22 / 9) +
      (5 / 7) * Q_K ^ 2 + (10 / 7) * Q_K := by
    simp only [CoverParams.Bv1, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243, k5Params_inv3,
      k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T]; ring
  ext
  · simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq]; field_simp [hw0_ne]; ring
  · simp only [Dual.add_eps, Dual.mul_val, Dual.mul_eps, Dual.pow_eq, Nat.cast_ofNat, Nat.reduceSub]
    rw [hw1_eq, hBv1_eq]; dsimp only [r1, rb_sc, S3Q, T59] at hcomb ⊢
    set c0_loc : K5 := (73 / 7971615 : K5) * (5 * T_K - 9) * (S_K - 3 * Q_K) ^ 2
    set dc0_loc : K5 := -(2 / 2121335325 : K5) * (5 * T_K - 9) * (-464630 * S_K + 1568725 * Q_K + 34020 * T_K - 23814) * (-S_K + 3 * Q_K)
    set c2_loc : K5 := (1 / 53457650190 : K5) * (5 * T_K - 9) *
      (-50137409 * S_K ^ 2 + 300824454 * S_K * Q_K - 451236681 * Q_K ^ 2 - 10001880 * S_K * T_K +
       30005640 * Q_K * T_K - 45873099 * S_K + 137619297 * Q_K - 10103940 * T_K + 58998753)
    set m01_loc : K5 := M01_q_fn S_K Q_K T_K * (5 * T_K - 9) * (S_K - 3 * Q_K) / 267288250950
    set Bv1_loc : K5 := (143 / 243 : K5) * S_K ^ 3 - (92 / 27) * S_K ^ 2 * Q_K + (52 / 9) * S_K * Q_K ^ 2 -
      (22 / 9) * Q_K ^ 3 + (143 / 243) * T_K ^ 3 - (92 / 27) * T_K ^ 2 + (52 / 9) * T_K - (22 / 9) +
      (5 / 7) * Q_K ^ 2 + (10 / 7) * Q_K
    set rb_loc : K5 := -(3 / 28 : K5) * (S_K - 3 * Q_K) * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)
    rw [show M01_q_fn S_K Q_K T_K * (5 * T_K - 9) * (S_K - 3 * Q_K) / (267288250950 * (S_K - 3 * Q_K) ^ 3) =
      m01_loc / (S_K - 3 * Q_K) ^ 3 by dsimp only [m01_loc]; rw [div_div]]
    have hcomb' : -2 * ((243 / 4 : K5) * Bv1_loc) * c0_loc + (rb_loc / 3) * dc0_loc + (S_K - 3 * Q_K) ^ 3 * c2_loc = m01_loc := hcomb
    rw [← hcomb']
    generalize c0_loc = v0; generalize dc0_loc = v1; generalize c2_loc = v2
    generalize Bv1_loc = vB; generalize rb_loc = vr
    generalize (S_K - 3 * Q_K) = s3q at hS3Q ⊢
    field_simp [hw0_ne, hS3Q]; ring


end SymmetricSexticResidual.LocalResidueInf

open scoped LaurentSeries in
theorem solution
    {U V aa rca ab b0s : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w0 w1 : SymmetricSexticResidual.K5Field.K5}
    (hw1_eq : w1 = w0 * ((243 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.CoverAlgebra.k5Params.Bv1 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0) (hab_eq : ab = rca * aa)
    (hU_D : QuadraticCovers.ValDual (-1) U (QuadraticCovers.Dual.C 1))
    (hV_D : QuadraticCovers.ValDual 1 V ⟨w0, w1⟩)
    (hrca_D : QuadraticCovers.ValDual 0 rca ⟨1 / 3, (-(3 / 28 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
      (119 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
       560 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
       630 * SymmetricSexticResidual.K5Field.Q_K ^ 2 + 90 * SymmetricSexticResidual.K5Field.Q_K + 90)) /
      (3 * (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)⟩)
    (haa_D : QuadraticCovers.ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : QuadraticCovers.ValDual 0 ab (⟨1 / 3, (-(3 / 28 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
      (119 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
       560 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
       630 * SymmetricSexticResidual.K5Field.Q_K ^ 2 + 90 * SymmetricSexticResidual.K5Field.Q_K + 90)) /
      (3 * (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩))
    (hb0_L : QuadraticCovers.ValLead 0 b0s
      (-((SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
        (5 * SymmetricSexticResidual.K5Field.T_K - 3)) /
        (3 * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9)))) :
    let fV : LaurentSeries SymmetricSexticResidual.K5Field.K5 → LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.A_0V (aa * z) (ab * z + b0s)
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K - aa * z * HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K - (ab * z + b0s) * HahnSeries.C SymmetricSexticResidual.K5Field.T_K) U V / V
    let S3Q := SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K
    let T59 := 5 * SymmetricSexticResidual.K5Field.T_K - 9
    QuadraticCovers.ValDual (-2) ((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6)
      ⟨w0⁻¹ ^ 2 * ((73 / 7971615 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2),
       w0⁻¹ ^ 2 * (SymmetricSexticResidual.LocalResidueInfAlg.M01_q_fn
         SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
         SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (267288250950 * S3Q ^ 3))⟩ :=
  SymmetricSexticResidual.LocalResidueInf.br1_inf_fV_lead3_valDual hw1_eq hw0_ne hab_eq hU_D hV_D hrca_D haa_D hab_D hb0_L
