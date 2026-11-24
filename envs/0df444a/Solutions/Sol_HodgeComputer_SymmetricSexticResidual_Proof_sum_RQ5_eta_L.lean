-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.sum_RQ5_eta_L
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T23:01:44.314651+00:00
-- url     : https://prove2.me/submissions/9ced6cdc-7963-4d2c-89f5-6323a9cf65f6

import Definitions.Def_HodgeComputerSSR_Q5ACDefs
import Definitions.Def_HodgeComputerSSR_Q5K5Master
import Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_simplePole_residue
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_poly_scaled
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_euler_weights
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_residue_eq_main
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_geom_bridge
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_p4_trace
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_BTot_dot_W
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_zero

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.LocalResidueU0
  SymmetricSexticResidual.Q5WeightsData QuadraticCovers
  CrossedRationalResidue Polynomial PolynomialEncoding.KroneckerCheck
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

private abbrev fac_4_ne := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled.1
private abbrev D_all_K5_ne := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled.2.1
private abbrev fac_4_eq_neg_L := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled.2.2.1

lemma sum_RQ5_eta_L_eq_BTot :
    ∑ r ∈ RQ5, CrossedRationalResidue.residue r eta_L =
      ιL_K5 (evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) * ((sc5_den * sc7_den : ℤ) : K5) /
        (81 * k5Params.Cv0 * (M_R_int : K5) * ((sc5_num * sc7_num : ℤ) : K5) *
          (D_int_all : K5) * evalSQ_K5 D_all_expr)) := by
  rw [Finset.sum_congr rfl HodgeComputer.SymmetricSexticResidual.Proof.localQ5_residue_eq_main, HodgeComputer.SymmetricSexticResidual.Proof.localQ5_p4_trace]
  set cK : K5 := 81 * k5Params.Cv0 * (M_R_int : K5)
  have hcK_ne : cK ≠ 0 := by
    have h81 : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
    have hMR : (M_R_int : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold M_R_int M_A_int L_all_A M_mid_int; decide)
    exact mul_ne_zero (mul_ne_zero h81 k5Params_Cv0_ne) hMR
  have hmap : mapRatFunc ιL_K5 (toRat R12_int_p / (RatFunc.C cK * toRat (k5Params.Q7_z * k5Params.Q5_z))) =
      algebraMap CoverL[X] (RatFunc CoverL) (R12_int_p.map ιL_K5) /
      algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.C (ιL_K5 cK) * (k5Params.Q7_z.map ιL_K5) * (k5Params.Q5_z.map ιL_K5)) := by
    simp only [map_div₀, map_mul, mapRatFunc_C, mapRatFunc_toRat,
      RatFunc.algebraMap_C, mul_assoc]
  rw [hmap]
  set D_L : CoverL[X] := Polynomial.C (ιL_K5 cK) * (k5Params.Q7_z.map ιL_K5) * (k5Params.Q5_z.map ιL_K5)
  have hres_r (r : CoverL) (hr : r ∈ RQ5) :
      CrossedRationalResidue.residue r
        (algebraMap CoverL[X] (RatFunc CoverL) (R12_int_p.map ιL_K5) /
         algebraMap CoverL[X] (RatFunc CoverL) D_L) =
      (R12_int_p.map ιL_K5).eval r /
        (ιL_K5 cK * (k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) := by
    have hr0 := mem_RQ5_iff.mp hr
    have hD0 : D_L.eval r = 0 := by simp [D_L, hr0]
    have hDd : D_L.derivative.eval r =
        ιL_K5 cK * (k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r := by
      simp only [D_L, mul_assoc, Polynomial.derivative_mul,
        Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, hr0, mul_zero, zero_add]
    have hDd_ne : D_L.derivative.eval r ≠ 0 := by
      rw [hDd]
      have h7 := eval_ne_zero_of_isCoprime isCoprime_Q5_Q7 hr0
      have hd5 := eval_ne_zero_of_isCoprime isCoprime_Q5_Q5_deriv hr0
      rw [← Polynomial.derivative_map] at hd5
      exact mul_ne_zero (mul_ne_zero ((map_ne_zero_iff _ ιL_K5.injective).mpr hcK_ne) h7) hd5
    rw [HodgeComputer.Formal.QuadraticCovers.simplePole_residue _ D_L r hD0 hDd_ne, hDd]
  rw [Finset.sum_congr rfl hres_r]
  have hR12_sum (r : CoverL) : (R12_int_p.map ιL_K5).eval r =
      ∑ k : Fin 13, ιL_K5 (R12_int_p.coeff k.val) * r ^ k.val := by
    have hdeg : (R12_int_p.map ιL_K5).natDegree < 13 :=
      lt_of_le_of_lt Polynomial.natDegree_map_le (by have := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_BTot_dot_W.2.2.2.2.1; omega)
    conv_lhs => rw [Polynomial.as_sum_range' (R12_int_p.map ιL_K5) 13 hdeg, ← Fin.sum_univ_eq_sum_range]
    rw [← Polynomial.coe_evalRingHom, map_sum]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_monomial, Polynomial.coeff_map]
  simp_rw [hR12_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  have hterm (k : Fin 13) :
      ∑ r ∈ RQ5, ιL_K5 (R12_int_p.coeff k.val) * r ^ k.val /
        (ιL_K5 cK * (k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) =
      ιL_K5 (R12_int_p.coeff k.val * W_K5_scaled k / cK) := by
    have h1 : ∀ r ∈ RQ5,
        ιL_K5 (R12_int_p.coeff k.val) * r ^ k.val /
          (ιL_K5 cK * (k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) =
        (ιL_K5 (R12_int_p.coeff k.val) / ιL_K5 cK) *
          (r ^ k.val / ((k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r)) := fun r _ => by ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, HodgeComputer.SymmetricSexticResidual.Proof.localQ5_euler_weights k]
    simp only [map_div₀, map_mul]; ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← map_sum]
  congr 1
  rw [HodgeComputer.SymmetricSexticResidual.Proof.localQ5_BTot_dot_W.2.2.2.2.2, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl; intro k _
  simp only [W_K5_scaled, W_K5, cK]; ring



theorem sum_RQ5_eta_L :
    ∑ r ∈ RQ5, CrossedRationalResidue.residue r eta_L = ιL_K5 (toK5_RQ5 / L_K ^ 2) := by
  rw [sum_RQ5_eta_L_eq_BTot]
  congr 1
  -- Evaluate `evalBivLK5 (evalTStep k5Ops S_K cacheK T_K) = 0`!
  have hstep0 := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_zero
  have hH0 := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_geom_bridge.gt_props.1
  have hCv0 := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_geom_bridge.gt_props.2.2.2.1
  have hCv0i := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_geom_bridge.gt_props.2.2.2.2.1
  have hRQ5_raw := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_BTot_dot_W.2.2.2.1
  have hD_all_eq := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_BTot_dot_W.2.2.1
  have hBTot_eq : (21 * S_K) ^ 2 * evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) =
      (C_RHS_int : K5) * (21 * S_K) ^ 2 * gtK.Cv0_int * cacheK.D_div_L2 * evalBivK5 RQ5_biv := by
    have hstep_eval : evalBivLK5 (evalTStep k5Ops S_K cacheK T_K) =
        (21 * S_K) ^ 2 * evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) -
        (C_RHS_int : K5) * (21 * S_K) ^ 2 * gtK.Cv0_int * cacheK.D_div_L2 * evalBivK5 RQ5_biv := by
      let P_ts : BivL K5 → Prop := fun b => evalBivLK5 b =
        (21 * S_K) ^ 2 * evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) -
        (C_RHS_int : K5) * (21 * S_K) ^ 2 * gtK.Cv0_int * cacheK.D_div_L2 * evalBivK5 RQ5_biv
      suffices h : P_ts (evalTStep k5Ops S_K cacheK T_K) from h
      unfold evalTStep
      refine letB_intro fun gt hgt => letB_intro fun B_tot hB =>
        letB_intro fun s21 hs21 => letB_intro fun t21 ht21 => letB_intro fun nh0 hnh0 =>
        letB_intro fun lhs hlhs => letB_intro fun rhs_sc hrsc => letB_intro fun rhs_raw hrraw => ?_
      dsimp only [P_ts]
      have hgt' : gt = gtK := by rw [hgt, HodgeComputer.SymmetricSexticResidual.Proof.localQ5_BTot_dot_W.1, HodgeComputer.SymmetricSexticResidual.Proof.localQ5_BTot_dot_W.2.1]; rfl
      rw [evalBivLK5_bivSub, evalBivLK5_bivSc, hlhs, hrsc, hrraw, hB, hRQ5_raw, hs21, ht21, hnh0, hgt']
      have hmul : ∀ a b : K5, k5Ops.mul a b = a * b := fun _ _ => rfl
      have hof : ∀ n : ℤ, k5Ops.ofInt n = (n : K5) := fun _ => rfl
      have hneg : ∀ a : K5, k5Ops.neg a = -a := fun _ => rfl
      simp only [hmul, hof, hneg, Int.cast_ofNat, hH0]
      rw [evalBivLK5_bivRedOnce, evalBivLK5_bivRedOnce]
      ring
    linear_combination hstep0 - hstep_eval
  have h21S_ne : (21 * S_K) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (by exact_mod_cast (by decide : (21 : ℕ) ≠ 0)) S_K_ne_zero)
  have hBTot_cancel : evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) =
      (C_RHS_int : K5) * gtK.Cv0_int * cacheK.D_div_L2 * ((D_RQ5 : K5) * toK5_RQ5) := by
    apply mul_left_cancel₀ h21S_ne
    have hDRQ5 : evalBivK5 RQ5_biv = (D_RQ5 : K5) * toK5_RQ5 := by
      rw [toK5_RQ5, mul_div_cancel₀ _ (Int.cast_ne_zero.mpr (by unfold D_RQ5; decide))]
    rw [hBTot_eq, hDRQ5]; ring
  -- Cancel `Cv0_int`, `cacheK.D_div_L2`, and match the exact integer constant identity via `by decide`!
  have hConstZ : C_RHS_int * D_RQ5 * (sc5_den * sc7_den) * 3 =
      (-25) * (sc5_num * sc7_num) * D_int_all * M_R_int := by
    unfold C_RHS_int D_RQ5 sc5_den sc7_den sc5_num sc7_num D_int_all M_R_int M_A_int L_all_A M_mid_int
    decide
  have hConstK : (C_RHS_int : K5) * (D_RQ5 : K5) * ((sc5_den * sc7_den : ℤ) : K5) * 3 =
      (-25 : K5) * ((sc5_num * sc7_num : ℤ) : K5) * (D_int_all : K5) * (M_R_int : K5) := by
    exact_mod_cast hConstZ
  have h81Cv0 : 81 * k5Params.Cv0 = (-(25 / 3 : K5)) * gtK.Cv0_int := by
    have h3 : (3 : K5) ≠ 0 := by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)
    apply mul_left_cancel₀ h3
    calc (3 : K5) * (81 * k5Params.Cv0) = 243 * k5Params.Cv0 := by ring
      _ = gtK.Cv0_243 := hCv0.symm
      _ = -25 * gtK.Cv0_int := hCv0i
      _ = 3 * (-(25 / 3 : K5) * gtK.Cv0_int) := by ring
  have hL_ne : L_K ≠ 0 := by
    intro h0; exact fac_4_ne (by rw [fac_4_eq_neg_L, h0, neg_zero])
  have hCv0i_ne : gtK.Cv0_int ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h81Cv0
    exact mul_ne_zero (by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)) k5Params_Cv0_ne h81Cv0
  have hDdiv_ne : cacheK.D_div_L2 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hD_all_eq; exact D_all_K5_ne hD_all_eq
  have hMR_ne : (M_R_int : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold M_R_int M_A_int L_all_A M_mid_int; decide)
  have hsc_ne : ((sc5_num * sc7_num : ℤ) : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold sc5_num sc7_num; decide)
  have hDint_ne : (D_int_all : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold D_int_all; decide)
  have h3_ne : (3 : K5) ≠ 0 := by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)
  have h25_ne : (-25 : K5) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast (by decide : (25 : ℕ) ≠ 0))
  rw [hBTot_cancel, hD_all_eq, h81Cv0]
  rw [div_eq_div_iff
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (by exact_mod_cast (by decide : (25 : ℕ) ≠ 0)) h3_ne)) hCv0i_ne)
      hMR_ne) hsc_ne) hDint_ne) (mul_ne_zero hDdiv_ne (pow_ne_zero 2 hL_ne)))
    (pow_ne_zero 2 hL_ne)]
  apply mul_left_cancel₀ h3_ne
  generalize (C_RHS_int : K5) = cR at hConstK ⊢
  generalize (D_RQ5 : K5) = cD at hConstK ⊢
  generalize ((sc5_den * sc7_den : ℤ) : K5) = cSD at hConstK ⊢
  generalize ((sc5_num * sc7_num : ℤ) : K5) = cSN at hConstK ⊢
  generalize (D_int_all : K5) = cDI at hConstK ⊢
  generalize (M_R_int : K5) = cMR at hConstK ⊢
  linear_combination (gtK.Cv0_int * cacheK.D_div_L2 * toK5_RQ5 * L_K ^ 2) * hConstK


end SymmetricSexticResidual.LocalResidueQ5

open scoped BigOperators in
theorem solution :
    ∑ r ∈ SymmetricSexticResidual.CoverResidue.RQ5,
      CrossedRationalResidue.residue r SymmetricSexticResidual.CoverResidue.eta_L =
      SymmetricSexticResidual.CoverResidue.ιL_K5
        (SymmetricSexticResidual.LocalResidueU0.toK5_RQ5 /
          SymmetricSexticResidual.LocalResidueU0.L_K ^ 2) :=
  SymmetricSexticResidual.LocalResidueQ5.sum_RQ5_eta_L
