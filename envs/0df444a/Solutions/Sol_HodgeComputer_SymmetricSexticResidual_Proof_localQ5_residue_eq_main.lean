-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_residue_eq_main
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:46:26.903964+00:00
-- url     : https://prove2.me/submissions/3bf3f7b7-8264-469a-8b7b-5eb5c61cbb8e

import Definitions.Def_HodgeComputerSSR_Q5ACDefs
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_reg_identities

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators

private abbrev nine_U_G_AC_eq := HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.nine_U_G_AC

lemma eta_AC_eq_main_add_reg : eta_AC = eta_AC_main + eta_AC_reg := by
  have hQ5_ne : polyC k5Params.Q5_z ≠ 0 := polyC_ne_zero Q5_K5_ne_zero
  have hQ7_ne : polyC k5Params.Q7_z ≠ 0 := polyC_ne_zero Q7_K5_ne_zero
  have hres_ne : pairC k5Params.res_z ≠ 0 := pairC_ne_zero_of_pnm nm_z_K5_ne_zero
  have h81_ne : (81 : A_C) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  have hAv0_ne : ιC_K5 k5Params.Av0 ≠ 0 := (map_ne_zero_iff _ ιC_K5.injective).mpr Av0_K5_ne_zero
  have h2W_ne : 2 * W_C + polyC k5Params.bW ≠ 0 := by
    intro h0
    have hsq : (2 * W_C + polyC k5Params.bW) ^ 2 = polyC k5Params.disc_E0 := by
      simp only [polyC, CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat]
      linear_combination 4 * W_C_relation
    rw [h0, zero_pow (by omega)] at hsq
    have hd_ne : k5Params.disc_E0 ≠ 0 := by
      intro hd0
      obtain ⟨u, v, huv⟩ := isCoprime_Q5_disc_E0
      rw [hd0, mul_zero, add_zero] at huv
      have hu : u ≠ 0 := fun hu0 => by simp [hu0] at huv
      have hdeg := congrArg Polynomial.natDegree huv
      rw [Polynomial.natDegree_one, Polynomial.natDegree_mul hu Q5_K5_ne_zero, Q5_K5_natDegree] at hdeg
      omega
    exact polyC_ne_zero hd_ne hsq.symm
  have hd22 : pairC k5Params.d2_2 = polyC k5Params.Q5_z := by
    simp [pairC, polyC, CoverParams.d2_2, PairAlg.map_ofScalar, evalAC_ofScalar]
  have hd33 : pairC k5Params.d3_3 = polyC k5Params.Q7_z := by
    simp [pairC, polyC, CoverParams.d3_3, PairAlg.map_ofScalar, evalAC_ofScalar]
  have hd1 : pairC k5Params.d1_z =
      remDeg3_d1 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
        (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_1) := by
    simp only [CoverParams.d1_z, CoverParams.pmul, remDeg3_d1, pairC,
      PairAlg.map_sub, PairAlg.map_mul, evalAC_sub, evalAC_mul]
  have hd0 : pairC k5Params.d0_z =
      remDeg3_d0 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
        (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_0) := by
    simp only [CoverParams.d0_z, CoverParams.pmul, remDeg3_d0, pairC,
      PairAlg.map_sub, PairAlg.map_mul, evalAC_sub, evalAC_mul]
  have hres : pairC k5Params.res_z =
      syl5 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
        (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_1) (pairC k5Params.d3_0) := by
    simp only [CoverParams.res_z, syl5Pair, syl5, pairC, PairAlg.map_add, PairAlg.map_sub,
      PairAlg.map_mul, PairAlg.map_smul, evalAC_add, evalAC_sub, evalAC_mul, evalAC_smul,
      map_ofNat]
    ring
  have hsplit := Q5_rem_split (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
    (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_1) (pairC k5Params.d3_0)
    (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1
    (interp4 P18_z_AC).2.2.2.1 (interp4 P18_z_AC).2.2.2.2
  rw [← hd1, ← hd0, ← hres, hd22, hd33] at hsplit
  simp only [eta_AC, eta_AC_num, eta_AC_main, eta_AC_reg, p4_AC, Q23_AC, hd22, hd33]
  have hcore :
      -(remDeg4_P1 (polyC k5Params.Q5_z) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
          (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1 (interp4 P18_z_AC).2.2.2.1 * pairC k5Params.d0_z -
        remDeg4_P0 (polyC k5Params.Q5_z) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
          (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1 (interp4 P18_z_AC).2.2.2.2 * pairC k5Params.d1_z) /
        (polyC k5Params.Q5_z ^ 3 * pairC k5Params.res_z) =
      -(interp4 P18_z_AC).1 / (polyC k5Params.Q7_z * polyC k5Params.Q5_z) +
      -Q23_of (polyC k5Params.Q5_z) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
        (polyC k5Params.Q7_z) (pairC k5Params.d3_2) (pairC k5Params.d3_1) (pairC k5Params.d3_0)
        (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1
        (interp4 P18_z_AC).2.2.2.1 (interp4 P18_z_AC).2.2.2.2 /
        (polyC k5Params.Q7_z * pairC k5Params.res_z) := by
    field_simp [hQ5_ne, hQ7_ne, hres_ne]
    linear_combination -hsplit
  have hfac := congrArg (fun t => t * (U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4 /
      (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW)))) hcore
  have hC_ne : 81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h81_ne hAv0_ne) h2W_ne
  calc _ = _ * (U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4 /
        (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW))) := by
          field_simp [hC_ne, hQ5_ne, hres_ne]
    _ = _ := hfac
    _ = _ := by field_simp [hC_ne, hQ5_ne, hQ7_ne, hres_ne]


-- Regularity of `trace_AC eta_AC_reg` at every `r ∈ RQ5`!
structure RegQ5 (r : CoverL) (x : A_C) : Prop where
  c0 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c0)
  c1 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c1)

lemma regQ5_evalAC {r : CoverL} {p : PairAlg (RatFunc K5)}
    (h0 : RegularAt r (mapRatFunc ιL_K5 p.c0)) (h1 : RegularAt r (mapRatFunc ιL_K5 p.c1)) :
    RegQ5 r (evalAC p) :=
  ⟨by rwa [coordsAC_evalAC], by rwa [coordsAC_evalAC]⟩

lemma regQ5_zero (r : CoverL) : RegQ5 r 0 := by
  rw [show (0 : A_C) = evalAC ⟨0, 0⟩ by simp [evalAC]]
  exact regQ5_evalAC (by simp [regAt_zero]) (by simp [regAt_zero])

lemma regQ5_one (r : CoverL) : RegQ5 r 1 := by
  rw [show (1 : A_C) = evalAC ⟨1, 0⟩ by simp [evalAC]]
  exact regQ5_evalAC (by simp [regAt_one]) (by simp [regAt_zero])

lemma regQ5_ofNat (r : CoverL) (n : ℕ) [n.AtLeastTwo] : RegQ5 r (no_index (OfNat.ofNat n)) := by
  have h1 : (OfNat.ofNat n : A_C) = evalAC ⟨(n : RatFunc K5), 0⟩ := by
    simp [evalAC, show (OfNat.ofNat n : A_C) = (n : A_C) from rfl]
  rw [h1]
  exact regQ5_evalAC (by rw [map_natCast]; exact ⟨Polynomial.C (n : CoverL), 1, by simp, by simp⟩) (by simp [regAt_zero])

lemma regQ5_ιC_K5 (r : CoverL) (c : K5) : RegQ5 r (ιC_K5 c) := by
  rw [show ιC_K5 c = evalAC ⟨RatFunc.C c, 0⟩ by simp [evalAC, ιC_K5]]
  exact regQ5_evalAC (by simp [mapRatFunc_C, regAt_C]) (by simp [regAt_zero])

lemma regQ5_polyC (r : CoverL) (P : K5[X]) : RegQ5 r (polyC P) := by
  rw [show polyC P = evalAC ⟨toRat P, 0⟩ by simp [evalAC, polyC]]
  exact regQ5_evalAC (by rw [mapRatFunc_toRat]; exact ⟨P.map ιL_K5, 1, by simp, by simp⟩) (by simp [regAt_zero])

lemma regQ5_pairC (r : CoverL) (p : PairAlg K5[X]) : RegQ5 r (pairC p) := by
  rw [pairC]
  exact regQ5_evalAC
    (by simp only [PairAlg.map, mapRatFunc_toRat]; exact ⟨p.c0.map ιL_K5, 1, by simp, by simp⟩)
    (by simp only [PairAlg.map, mapRatFunc_toRat]; exact ⟨p.c1.map ιL_K5, 1, by simp, by simp⟩)

lemma regQ5_U_C (r : CoverL) : RegQ5 r U_C := by
  simpa [polyC, U_C, toRat] using regQ5_polyC r Polynomial.X

lemma regQ5_W_C (r : CoverL) : RegQ5 r W_C := by
  rw [← evalAC_W]
  exact regQ5_evalAC (by simp [PairAlg.W, regAt_zero]) (by simp [PairAlg.W, regAt_one])

lemma regQ5_add {r : CoverL} {x y : A_C} (hx : RegQ5 r x) (hy : RegQ5 r y) : RegQ5 r (x + y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_add]
  exact regQ5_evalAC
    (by simp only [PairAlg.add, map_add]; exact hx.1.add hy.1)
    (by simp only [PairAlg.add, map_add]; exact hx.2.add hy.2)

lemma regQ5_neg {r : CoverL} {x : A_C} (hx : RegQ5 r x) : RegQ5 r (-x) := by
  rw [← evalAC_coordsAC x, ← evalAC_neg]
  exact regQ5_evalAC (by simp only [PairAlg.neg, map_neg]; exact regAt_neg_local hx.1)
    (by simp only [PairAlg.neg, map_neg]; exact regAt_neg_local hx.2)

lemma regQ5_sub {r : CoverL} {x y : A_C} (hx : RegQ5 r x) (hy : RegQ5 r y) : RegQ5 r (x - y) := by
  rw [sub_eq_add_neg]; exact regQ5_add hx (regQ5_neg hy)

lemma regQ5_mul {r : CoverL} {x y : A_C} (hx : RegQ5 r x) (hy : RegQ5 r y) : RegQ5 r (x * y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_mul]
  have hb : RegularAt r (mapRatFunc ιL_K5 (toRat k5Params.bW)) := by
    rw [mapRatFunc_toRat]; exact ⟨k5Params.bW.map ιL_K5, 1, by simp, by simp⟩
  have hc : RegularAt r (mapRatFunc ιL_K5 (toRat k5Params.cW)) := by
    rw [mapRatFunc_toRat]; exact ⟨k5Params.cW.map ιL_K5, 1, by simp, by simp⟩
  exact regQ5_evalAC
    (by simp only [PairAlg.mul, map_sub, map_mul]; exact regAt_sub_local (regAt_mul_local hx.1 hy.1) (regAt_mul_local (regAt_mul_local hx.2 hy.2) hc))
    (by simp only [PairAlg.mul, map_add, map_sub, map_mul]; exact regAt_sub_local (regAt_add_local (regAt_mul_local hx.1 hy.2) (regAt_mul_local hx.2 hy.1)) (regAt_mul_local (regAt_mul_local hx.2 hy.2) hb))
where
  regAt_add_local {f g : RatFunc CoverL} (hf : RegularAt r f) (hg : RegularAt r g) : RegularAt r (f + g) := hf.add hg

lemma regQ5_pow {r : CoverL} {x : A_C} (hx : RegQ5 r x) (n : ℕ) : RegQ5 r (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact regQ5_one r
  | succ k ih => rw [pow_succ]; exact regQ5_mul ih hx

lemma regQ5_div_polyC {r : CoverL} {x : A_C} {P : K5[X]} (hx : RegQ5 r x)
    (hP : (P.map ιL_K5).eval r ≠ 0) : RegQ5 r (x / polyC P) := by
  have h1 : x / polyC P = evalAC (PairAlg.smul (toRat P)⁻¹ (coordsAC x)) := by
    rw [evalAC_smul, evalAC_coordsAC, map_inv₀, div_eq_inv_mul]; rfl
  rw [h1]
  have hinv : RegularAt r (mapRatFunc ιL_K5 (toRat P)⁻¹) := by
    rw [map_inv₀, mapRatFunc_toRat]
    exact ⟨1, P.map ιL_K5, hP, by simp⟩
  exact regQ5_evalAC
    (by simp only [PairAlg.smul, map_mul]; exact regAt_mul_local hinv hx.1)
    (by simp only [PairAlg.smul, map_mul]; exact regAt_mul_local hinv hx.2)

lemma regQ5_div_pairC {r : CoverL} {x : A_C} {y : PairAlg K5[X]} (hx : RegQ5 r x)
    (hnm : ((k5Params.pnm y).map ιL_K5).eval r ≠ 0) : RegQ5 r (x / pairC y) := by
  have hy_conj : pairC y * pairC (PairAlg.conj k5Params.bW y) = polyC (k5Params.pnm y) := by
    simp only [pairC, polyC, ← evalAC_mul, ← evalAC_ofScalar]
    congr 1; ext <;> (simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map,
      CoverParams.pnm, PairAlg.nm, map_add, map_sub, map_neg, map_mul, map_pow]; ring)
  have hnm_ne : k5Params.pnm y ≠ 0 := fun h0 => hnm (by simp [h0])
  have hconj_ne : pairC (PairAlg.conj k5Params.bW y) ≠ 0 := fun h0 =>
    polyC_ne_zero hnm_ne (by rw [← hy_conj, h0, mul_zero])
  have heq : x / pairC y = (x * pairC (PairAlg.conj k5Params.bW y)) / polyC (k5Params.pnm y) := by
    rw [← hy_conj, mul_div_mul_right _ _ hconj_ne]
  rw [heq]
  exact regQ5_div_polyC (regQ5_mul hx (regQ5_pairC r _)) hnm

lemma regQ5_div_nat {r : CoverL} {x : A_C} (hx : RegQ5 r x) (n : ℕ) [hn : n.AtLeastTwo] :
    RegQ5 r (x / no_index (OfNat.ofNat n)) := by
  have heq : (OfNat.ofNat n : A_C) = polyC (Polynomial.C (n : K5)) := by
    simp [polyC, toRat, show (OfNat.ofNat n : A_C) = (n : A_C) from rfl]
  rw [heq]
  apply regQ5_div_polyC hx
  simp only [Polynomial.map_natCast, Polynomial.eval_natCast, map_natCast]
  exact (Nat.cast_ne_zero (R := CoverL)).mpr (NeZero.ne n)

lemma regularAt_trace_eta_AC_reg (r : CoverL) (hr : r ∈ RQ5) :
    RegularAt r (mapRatFunc ιL_K5 (Algebra.trace (RatFunc K5) A_C eta_AC_reg)) := by
  have hQ5_0 := mem_RQ5_iff.mp hr
  have hr0 : r ≠ 0 := fun h0 => zero_notMem_RQ5 (h0 ▸ hr)
  have hr1 : r ≠ 1 := by
    have h := eval_ne_zero_of_isCoprime isCoprime_Q5_X_sub_1 hQ5_0
    simpa [sub_eq_zero] using h
  have hcb_ne : (k5Params.cb_h.map ιL_K5).eval r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_Q5_cb_h hQ5_0
  have hQ7_ne : (k5Params.Q7_z.map ιL_K5).eval r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_Q5_Q7 hQ5_0
  have hnmWU_ne : (k5Params.nm_WU.map ιL_K5).eval r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_Q5_nm_WU hQ5_0
  have hP34_ne : (P34_K5.map ιL_K5).eval r ≠ 0 := fun h => Finset.disjoint_left.mp disjoint_R34_RQ5 (mem_R34_iff.mpr h) hr
  have hnm_z_ne : (k5Params.nm_z.map ιL_K5).eval r ≠ 0 := by
    rw [nm_z_K5_factor]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    have hcbm_ne : (cb_h_m_K5.map ιL_K5).eval r ≠ 0 := by
      have h := congrArg (fun p : K5[X] => (p.map ιL_K5).eval r) cb_h_K5_eq_mul_monic
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C] at h
      rw [h] at hcb_ne; exact right_ne_zero_of_mul hcb_ne
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((map_ne_zero_iff _ ιL_K5.injective).mpr lc34_K5_ne_zero)
      (pow_ne_zero 15 hr0)) (pow_ne_zero 12 hcbm_ne)) hP34_ne
  have hcW_ne : (k5Params.cW.map ιL_K5).eval r ≠ 0 := cW_eval_ne_zero hr0
  -- Show `W_C`, `V_C`, `u_of U_C`, `v_of V_C` are invertible in `RegQ5 r`!
  have hU_reg : RegQ5 r U_C := regQ5_U_C r
  have hW_reg : RegQ5 r W_C := regQ5_W_C r
  have hV_reg : RegQ5 r V_C := by
    rw [V_C, show U_C = polyC Polynomial.X by simp [U_C, polyC, toRat]]
    exact regQ5_div_polyC hW_reg (by simpa using hr0)
  have hdiv_W {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / W_C) := by
    rw [show W_C = pairC PairAlg.W by rw [← evalAC_W, pairC]; congr 1; ext <;> simp [PairAlg.W, PairAlg.map]]
    exact regQ5_div_pairC hx (by simpa [CoverParams.pnm, PairAlg.nm, PairAlg.W] using hcW_ne)
  have hdiv_U {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / U_C) := by
    rw [show U_C = polyC Polynomial.X by simp [U_C, polyC, toRat]]
    exact regQ5_div_polyC hx (by simpa using hr0)
  have hdiv_V {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / V_C) := by
    rw [V_C, div_div_eq_mul_div]; exact hdiv_W (regQ5_mul hx hU_reg)
  have hdiv_u {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / u_of U_C) := by
    have hu : u_of U_C = polyC (Polynomial.X - 1) / 9 := by
      simp [u_of, U_C, polyC, toRat]
    rw [hu, div_div_eq_mul_div]
    exact regQ5_div_polyC (regQ5_mul hx (regQ5_ofNat r 9)) (by simpa [sub_eq_zero] using hr1)
  have hdiv_v {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / v_of V_C) := by
    have hv : v_of V_C = pairC (PairAlg.sub PairAlg.W (PairAlg.ofScalar Polynomial.X)) / (9 * U_C) := by
      simp only [v_of, V_C, pairC, PairAlg.map_sub, PairAlg.map_W, PairAlg.map_ofScalar,
        evalAC_sub, evalAC_W, evalAC_ofScalar, U_C, toRat, RatFunc.algebraMap_X]
      have hU := U_C_ne_zero; rw [U_C] at hU; field_simp [hU]
    rw [hv, div_div_eq_mul_div]
    exact regQ5_div_pairC (regQ5_mul hx (regQ5_mul (regQ5_ofNat r 9) hU_reg)) (by
      have hpair : PairAlg.sub PairAlg.W (PairAlg.ofScalar (Polynomial.X : K5[X])) = ⟨-Polynomial.X, 1⟩ := by
        ext <;> simp [PairAlg.sub, PairAlg.W, PairAlg.ofScalar]
      rw [hpair]; exact hnmWU_ne)
  -- Prove `RegQ5 r (P18_z_AC z)` for any `z` with `RegQ5 r z`!
  have hP18_gen (a b : A_C) (ha : RegQ5 r a) (hb : RegQ5 r b) :
      RegQ5 r (P18_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) a b U_C V_C) := by
    have hS := regQ5_ιC_K5 r S_K; have hQ := regQ5_ιC_K5 r Q_K; have hT := regQ5_ιC_K5 r T_K
    have hx := regQ5_ιC_K5 r x_K; have hy := regQ5_ιC_K5 r y_K
    have hξS := regQ5_sub hS (regQ5_mul ha hT)
    have hξQ := regQ5_sub hQ (regQ5_mul hb hT)
    have hdHS (s q : A_C) (hs : RegQ5 r s) (hq : RegQ5 r q) : RegQ5 r (dH_dS s q U_C V_C) := by
      dsimp only [dH_dS]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hs | exact hq | exact hU_reg | exact hV_reg | exact regQ5_ofNat r _)
    have hdHQ (s q v0 : A_C) (hs : RegQ5 r s) (hq : RegQ5 r q) (hv0 : RegQ5 r v0) : RegQ5 r (dH_dQ s q v0 U_C V_C) := by
      dsimp only [dH_dQ]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hs | exact hq | exact hv0 | exact hU_reg | exact hV_reg | exact regQ5_ofNat r _)
    have hnumM (mi : Fin 10) : RegQ5 r (numM mi a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C) := by
      have ha2 : RegQ5 r (q1_a2 a b U_C V_C) := hdHS _ _ ha hb
      have ha0 : RegQ5 r (q1_a0 _ _ U_C V_C) := hdHS _ _ hξS hξQ
      have ha1 : RegQ5 r (q1_a1 _ _ _ _ U_C V_C) := regQ5_sub (regQ5_sub (hdHS _ _ (regQ5_add ha hξS) (regQ5_add hb hξQ)) ha2) ha0
      have hb2 : RegQ5 r (q2_b2 a b U_C V_C) := hdHQ _ _ 0 ha hb (regQ5_zero r)
      have hb0 : RegQ5 r (q2_b0 _ _ U_C V_C) := hdHQ _ _ 1 hξS hξQ (regQ5_one r)
      have hb1 : RegQ5 r (q2_b1 _ _ _ _ U_C V_C) :=
        regQ5_add (regQ5_sub (regQ5_sub (hdHQ _ _ 0 (regQ5_add ha hξS) (regQ5_add hb hξQ) (regQ5_zero r)) hb2)
          (hdHQ _ _ 0 hξS hξQ (regQ5_zero r)))
          (regQ5_mul (regQ5_mul (regQ5_mul (regQ5_div_nat (regQ5_ofNat r 10) 7) hb) hU_reg) hV_reg)
      have hd20 := regQ5_sub (regQ5_mul ha2 hb0) (regQ5_mul ha0 hb2)
      have hd21 := regQ5_sub (regQ5_mul ha2 hb1) (regQ5_mul ha1 hb2)
      have hd10 := regQ5_sub (regQ5_mul ha1 hb0) (regQ5_mul ha0 hb1)
      fin_cases mi <;> dsimp only [numM, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | exact hd10 | exact hd20 | exact hd21 | exact hξS | exact hξQ | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact ha | exact hb | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
    have hM0 : RegQ5 r (A_0U a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C / U_C +
        A_0V a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C / V_C) := by
      refine regQ5_add (hdiv_U ?_) (hdiv_V ?_)
      · dsimp only [A_0U]
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hnumM _ | exact regQ5_ofNat r _)
      · dsimp only [A_0V]
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hnumM _ | exact regQ5_ofNat r _)
    have hAY : RegQ5 r (A_Y a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C) := by
      dsimp only [A_Y]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hU_reg | exact hV_reg | exact hnumM _ | exact regQ5_ofNat r _)
    have hAX : RegQ5 r (A_X a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C) := by
      dsimp only [A_X]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hU_reg | exact hnumM _ | exact regQ5_ofNat r _)
    have hu_r : RegQ5 r (u_of U_C) := regQ5_div_nat (regQ5_sub hU_reg (regQ5_one r)) 9
    have hv_r : RegQ5 r (v_of V_C) := regQ5_div_nat (regQ5_sub hV_reg (regQ5_one r)) 9
    have hH0 : RegQ5 r (H0_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)) := by
      dsimp only [H0_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hT | exact regQ5_ofNat r _)
    have hdH0 (k : Fin 3) : RegQ5 r (dH0_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)) := by
      fin_cases k <;> dsimp only [dH0_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hT | exact regQ5_ofNat r _)
    have hdF5 (k : Fin 5) : RegQ5 r (dF5_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)) := by
      fin_cases k <;> dsimp only [dF5_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_add | apply regQ5_mul | apply regQ5_pow | exact hS | exact hT | exact hx | exact hy | exact hdH0 _ | exact regQ5_ofNat r _)
    have hu3 : RegQ5 r (u3_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) := by
      dsimp only [u3_of]; exact regQ5_add (regQ5_sub hx hS) (regQ5_mul (regQ5_ofNat r 2) hQ)
    have hv3 : RegQ5 r (v3_of (ιC_K5 T_K) (ιC_K5 y_K)) := by
      dsimp only [v3_of]; exact regQ5_add (regQ5_sub hy hT) (regQ5_ofNat r 2)
    have hDX2 : RegQ5 r (DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) := by
      dsimp only [DX2_of]
      repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hu3 | exact regQ5_ofNat r _)
    have hDY2 : RegQ5 r (DY2_of (ιC_K5 T_K) (ιC_K5 y_K)) := by
      dsimp only [DY2_of]
      repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact hT | exact hv3 | exact regQ5_ofNat r _)
    have hdDX2 (k : Fin 5) : RegQ5 r (dDX2_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) := by
      fin_cases k <;> dsimp only [dDX2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hu3 | exact regQ5_zero r | exact regQ5_ofNat r _)
    have hdDY2 (k : Fin 5) : RegQ5 r (dDY2_fn k (ιC_K5 T_K) (ιC_K5 y_K)) := by
      fin_cases k <;> dsimp only [dDY2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hT | exact hv3 | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
    have hLX : RegQ5 r (LX_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) U_C) := by
      dsimp only [LX_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | exact hu_r | exact hS | exact hQ | exact hu3 | exact hU_reg | exact regQ5_ofNat r _)
    have hLY : RegQ5 r (LY_of (ιC_K5 T_K) (ιC_K5 y_K) V_C) := by
      dsimp only [LY_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | exact hv_r | exact hT | exact hv3 | exact hV_reg | exact regQ5_ofNat r _)
    have hdLX (k : Fin 5) : RegQ5 r (dLX_fn k U_C) := by
      fin_cases k <;> dsimp only [dLX_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hu_r | exact hU_reg | exact regQ5_zero r | exact regQ5_ofNat r _)
    have hdLY (k : Fin 5) : RegQ5 r (dLY_fn k V_C) := by
      fin_cases k <;> dsimp only [dLY_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_neg | apply regQ5_mul | exact hv_r | exact hV_reg | exact regQ5_zero r | exact regQ5_ofNat r _)
    have hbr (k : Fin 5) : RegQ5 r (br_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) := by
      dsimp only [br_fn]
      refine regQ5_add ?_ (regQ5_mul (regQ5_mul (regQ5_mul (regQ5_ofNat r 2) hS) hT)
        (regQ5_sub (regQ5_mul hLX (hdLY k)) (regQ5_mul hLY (hdLX k))))
      fin_cases k
      · exact regQ5_mul (regQ5_mul (regQ5_neg hT) hLX) hLY
      · exact regQ5_zero r
      · exact regQ5_mul (regQ5_mul hS hLX) hLY
      · exact regQ5_zero r
      · exact regQ5_zero r
    have hom (i j : Fin 5) : RegQ5 r (om_fn i j (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) := by
      dsimp only [om_fn]
      have homX (k : Fin 5) : RegQ5 r (match k with
          | 0 => -25 * ιC_K5 S_K * U_C + 15 * ιC_K5 Q_K * U_C + 9 * ιC_K5 x_K * U_C + 25 * ιC_K5 S_K - 15 * ιC_K5 Q_K
          | 1 => 30 * (U_C - 1) * ιC_K5 S_K
          | 3 => 18 * U_C * ιC_K5 S_K
          | _ => 0) := by
        split <;> repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hS | exact hQ | exact hx | exact hU_reg | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
      have homY (k : Fin 5) : RegQ5 r (match k with
          | 2 => -25 * ιC_K5 T_K * V_C + 9 * ιC_K5 y_K * V_C + 25 * ιC_K5 T_K + 15 * V_C - 15
          | 4 => 18 * V_C * ιC_K5 T_K
          | _ => 0) := by
        split <;> repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hT | exact hy | exact hV_reg | exact regQ5_zero r | exact regQ5_ofNat r _)
      exact regQ5_mul (regQ5_div_nat (regQ5_one r) 81)
        (regQ5_sub (regQ5_mul (homX i) (homY j)) (regQ5_mul (homX j) (homY i)))
    have hFc (f2 : Fin 5 → Fin 5 → A_C) (hf2 : ∀ p q, RegQ5 r (f2 p q)) (i : Fin 3) :
        RegQ5 r (F_contract (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) f2 i) := by
      fin_cases i <;> dsimp only [F_contract, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        exact regQ5_add (regQ5_add (regQ5_mul (hdF5 4) (hf2 _ 3)) (regQ5_mul (hdF5 3) (hf2 4 _)))
          (regQ5_mul (hdF5 _) (hf2 3 4))
    have hdot (v : Fin 3 → A_C) (hv : ∀ i, RegQ5 r (v i)) : RegQ5 r (dot_ab v a b) :=
      regQ5_add (regQ5_add (regQ5_mul (hv 0) ha) (regQ5_mul (hv 1) hb)) (hv 2)
    have hqY : RegQ5 r (dot_ab (QY_num (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) a b / v_of V_C) :=
      hdiv_v (hdot _ fun i => regQ5_mul hDY2 (regQ5_sub
        (regQ5_mul hDX2 (hFc _ (fun p q => regQ5_mul (regQ5_mul hS hT) (hom p q)) i))
        (hFc _ (fun p q => regQ5_mul (regQ5_mul hS hT)
          (regQ5_sub (regQ5_mul (hdDX2 p) (hbr q)) (regQ5_mul (hdDX2 q) (hbr p)))) i)))
    have hqX : RegQ5 r (dot_ab (QX_num (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) a b / u_of U_C) :=
      hdiv_u (hdot _ fun i => regQ5_mul hDX2 (regQ5_add
        (regQ5_mul (regQ5_neg hDY2) (hFc _ (fun p q => regQ5_mul (regQ5_mul hS hT) (hom p q)) i))
        (hFc _ (fun p q => regQ5_mul (regQ5_mul hS hT)
          (regQ5_sub (regQ5_mul (hdDY2 p) (hbr q)) (regQ5_mul (hdDY2 q) (hbr p)))) i)))
    have hA1 : RegQ5 r (A1_of (ιC_K5 S_K) (ιC_K5 Q_K) U_C V_C) := by
      dsimp only [A1_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hU_reg | exact hV_reg | exact regQ5_one r | exact regQ5_ofNat r _)
    have hB1 : RegQ5 r (B1_of (ιC_K5 T_K) U_C V_C) := by
      dsimp only [B1_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact hT | exact hU_reg | exact hV_reg | exact regQ5_one r | exact regQ5_ofNat r _)
    have hdA1 (k : Fin 3) : RegQ5 r (dA1_fn k (ιC_K5 S_K) (ιC_K5 Q_K) U_C V_C) := by
      fin_cases k <;> dsimp only [dA1_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hU_reg | exact hV_reg | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
    have hcA1 : RegQ5 r (cA1_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) a b U_C V_C) := by
      dsimp only [cA1_of]
      repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | exact hH0 | exact hA1 | exact ha | exact hb | exact hdA1 _ | exact hdH0 _)
    have hEB : RegQ5 r (EB_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) := by
      dsimp only [EB_of, W2_of]
      repeat' (with_reducible first | apply regQ5_sub | apply regQ5_mul | exact hS | exact hT | exact hDX2 | exact hDY2 | exact hdF5 _ | exact hbr _ | exact regQ5_ofNat r _)
    dsimp only [P18_of]
    exact regQ5_add
      (regQ5_mul hM0 (regQ5_add (regQ5_add (regQ5_mul (regQ5_mul hH0 hA1) hqY) (regQ5_mul (regQ5_mul hH0 hB1) hqX))
        (regQ5_mul (hdiv_v hcA1) hEB)))
      (regQ5_mul (regQ5_add (regQ5_mul hAY hqY) (regQ5_mul hAX hqX)) (regQ5_pow hH0 2))
  have hP18_reg (z : A_C) (hz : RegQ5 r z) : RegQ5 r (P18_z_AC z) := by
    have ha : RegQ5 r (z / W_C) := hdiv_W hz
    have hb : RegQ5 r (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)) := by
      rw [← div_div]
      exact regQ5_div_polyC (hdiv_W (regQ5_neg (regQ5_add (regQ5_mul (regQ5_polyC r _) hz) (regQ5_pairC r _)))) hcb_ne
    exact hP18_gen _ _ ha hb
  -- All 5 interpolated coefficients of `P18_z_AC` are `RegQ5 r`!
  have hp0 := hP18_reg 0 (regQ5_zero r)
  have hp1 := hP18_reg 1 (regQ5_one r)
  have hpm1 := hP18_reg (-1) (regQ5_neg (regQ5_one r))
  have hp2 := hP18_reg 2 (regQ5_ofNat r 2)
  have hpm2 := hP18_reg (-2) (regQ5_neg (regQ5_ofNat r 2))
  have hq4 : RegQ5 r (interp4 P18_z_AC).1 := by
    dsimp only [interp4]
    exact regQ5_div_nat (regQ5_add (regQ5_add (regQ5_mul (regQ5_neg (regQ5_ofNat r 4)) (regQ5_add hp1 hpm1))
      (regQ5_add hp2 hpm2)) (regQ5_mul (regQ5_ofNat r 6) hp0)) 24
  have hq3 : RegQ5 r (interp4 P18_z_AC).2.1 := by
    dsimp only [interp4]
    exact regQ5_div_nat (regQ5_add (regQ5_mul (regQ5_neg (regQ5_ofNat r 2)) (regQ5_sub hp1 hpm1))
      (regQ5_sub hp2 hpm2)) 12
  have hq2 : RegQ5 r (interp4 P18_z_AC).2.2.1 := by
    dsimp only [interp4]
    exact regQ5_div_nat (regQ5_sub (regQ5_sub (regQ5_mul (regQ5_ofNat r 16) (regQ5_add hp1 hpm1))
      (regQ5_add hp2 hpm2)) (regQ5_mul (regQ5_ofNat r 30) hp0)) 24
  have hq1 : RegQ5 r (interp4 P18_z_AC).2.2.2.1 := by
    dsimp only [interp4]
    exact regQ5_div_nat (regQ5_sub (regQ5_mul (regQ5_ofNat r 8) (regQ5_sub hp1 hpm1))
      (regQ5_sub hp2 hpm2)) 12
  have hq0 : RegQ5 r (interp4 P18_z_AC).2.2.2.2 := hp0
  have hQ23 : RegQ5 r Q23_AC := by
    dsimp only [Q23_AC, Q23_of]
    repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact regQ5_pairC r _ | exact hq4 | exact hq3 | exact hq2 | exact hq1 | exact hq0 | exact regQ5_ofNat r _)
  have hnum : RegQ5 r (-(Q23_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
      (81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q7_z * pairC k5Params.res_z)) := by
    have htop := regQ5_neg (regQ5_mul (regQ5_mul (regQ5_mul hQ23 (regQ5_pow hU_reg 3)) hW_reg) (regQ5_pow (regQ5_polyC r k5Params.cb_h) 4))
    have h81Av0 : 81 * ιC_K5 k5Params.Av0 = polyC (Polynomial.C (81 * k5Params.Av0)) := by
      simp [polyC, ιC_K5, toRat, RatFunc.algebraMap_C, map_ofNat]
    rw [h81Av0, ← div_div, ← div_div]
    apply regQ5_div_pairC _ hnm_z_ne
    apply regQ5_div_polyC _ hQ7_ne
    apply regQ5_div_polyC htop
    rw [Polynomial.map_C, Polynomial.eval_C, map_mul, map_ofNat]
    have h81 : (81 : CoverL) ≠ 0 := by
      have h : ((81 : ℕ) : CoverL) ≠ 0 := (Nat.cast_ne_zero (R := CoverL)).mpr (by decide)
      rwa [Nat.cast_ofNat] at h
    exact mul_ne_zero h81 ((map_ne_zero_iff _ ιL_K5.injective).mpr Av0_K5_ne_zero)
  -- Apply `trace_AC_euler` with `y = PairAlg.one`!
  set x_reg := -(Q23_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
    (81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q7_z * pairC k5Params.res_z)
  have heta_eq : eta_AC_reg = evalAC (coordsAC x_reg) /
      (evalAC (PairAlg.ofScalar (1 : RatFunc K5)) * (2 * W_C + ιC_rat (toRat k5Params.bW))) := by
    rw [evalAC_coordsAC, evalAC_ofScalar, map_one, one_mul]
    have hmul : ∀ a b c d e : A_C, a / (b * c * d * e) = (a / (b * d * e)) / c := fun a b c d e => by
      rw [div_div]; congr 1; ring
    exact hmul (-(Q23_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4))
      (81 * ιC_K5 k5Params.Av0) (2 * W_C + polyC k5Params.bW)
      (polyC k5Params.Q7_z) (pairC k5Params.res_z)
  rw [heta_eq, trace_AC_euler (coordsAC x_reg) (PairAlg.ofScalar 1) (by simp [PairAlg.nm, PairAlg.ofScalar])]
  simp only [PairAlg.nm, PairAlg.ofScalar, one_pow, zero_pow (by omega : 2 ≠ 0),
    zero_mul, mul_zero, add_zero, sub_zero, mul_one, div_one]
  exact hnum.2

lemma residue_eta_L_eq_main (r : CoverL) (hr : r ∈ RQ5) :
    CrossedRationalResidue.residue r eta_L =
      CrossedRationalResidue.residue r (mapRatFunc ιL_K5 (Algebra.trace (RatFunc K5) A_C eta_AC_main)) := by
  simp only [CoverResidue.eta_L, CoverResidue.eta, eta_AC_eq_main_add_reg, map_add]
  rw [(regularAt_trace_eta_AC_reg r hr).residue_eq_zero, add_zero]



end SymmetricSexticResidual.LocalResidueQ5

theorem solution
    (r : SymmetricSexticResidual.CoverResidue.CoverL)
    (hr : r ∈ SymmetricSexticResidual.CoverResidue.RQ5) :
    CrossedRationalResidue.residue r SymmetricSexticResidual.CoverResidue.eta_L =
      CrossedRationalResidue.residue r
        (QuadraticCovers.mapRatFunc SymmetricSexticResidual.CoverResidue.ιL_K5
          (Algebra.trace (RatFunc SymmetricSexticResidual.K5Field.K5)
            SymmetricSexticResidual.CoverResidue.A_C
            SymmetricSexticResidual.LocalResidueQ5.eta_AC_main)) :=
  SymmetricSexticResidual.LocalResidueQ5.residue_eta_L_eq_main r hr
