-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.sheet_horiz_identity
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:53:57.024014+00:00
-- url     : https://prove2.me/submissions/f857ba9d-66d3-453a-88ae-cee289270bc2

import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace SymmetricSexticResidual.SheetCalculus
open SymmetricSexticResidual SymmetricSexticResidual.K5Field
open MvPolynomial
open scoped BigOperators Matrix

section SheetL
variable {L : Type*} [Field L] [CharZero L] [Algebra K5 L] [FiniteDimensional K5 L]

-- Generic derivation helpers on L (zero side-condition hypotheses!)
omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma ofNat_ne_zero_L (n : ℕ) [hn : n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : L) ≠ 0 := by
  change (n : L) ≠ 0
  exact Nat.cast_ne_zero.mpr (by have := hn.prop; omega)

omit [CharZero L] [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_ofNat (D : Derivation ℤ L L) (n : ℕ) [n.AtLeastTwo] :
    D (no_index (OfNat.ofNat n)) = 0 := by
  change D (n : L) = 0; exact D.map_natCast n

omit [CharZero L] [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_div (D : Derivation ℤ L L) (a b : L) (hb : b ≠ 0) :
    D (a / b) = (b * D a - a * D b) / b ^ 2 := by
  have h := congrArg D (div_mul_cancel₀ a hb)
  rw [D.leibniz] at h; simp only [smul_eq_mul] at h
  have h2 := congrArg (b * ·) h
  rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hb] at h2
  rw [eq_div_iff (pow_ne_zero 2 hb)]; linear_combination h2

omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_ofNat_div (D : Derivation ℤ L L) (a b : ℕ) [a.AtLeastTwo] [b.AtLeastTwo] :
    D ((no_index (OfNat.ofNat a) : L) / (no_index (OfNat.ofNat b) : L)) = 0 := by
  rw [D_div D _ _ (ofNat_ne_zero_L b), D_ofNat, D_ofNat]; ring

omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_one_div (D : Derivation ℤ L L) (b : ℕ) [b.AtLeastTwo] :
    D ((1 : L) / (no_index (OfNat.ofNat b) : L)) = 0 := by
  rw [D_div D _ _ (ofNat_ne_zero_L b), D.map_one_eq_zero, D_ofNat]; ring


omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_kills_dH_dS (D : Derivation ℤ L L) (s q U V : L)
    (hs : D s = 0) (hq : D q = 0) (hU : D U = 0) (hV : D V = 0) :
    D (dH_dS s q U V) = 0 := by
  simp only [dH_dS, map_add, map_sub, map_neg, D.leibniz, D.leibniz_pow, hs, hq, hU, hV,
    D_ofNat, D_ofNat_div, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]

omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_kills_dH_dQ (D : Derivation ℤ L L) (s q v0 U V : L)
    (hs : D s = 0) (hq : D q = 0) (hv0 : D v0 = 0) (hU : D U = 0) (hV : D V = 0) :
    D (dH_dQ s q v0 U V) = 0 := by
  simp only [dH_dQ, map_add, map_sub, map_neg, D.leibniz, D.leibniz_pow, hs, hq, hv0, hU, hV,
    D_ofNat, D_ofNat_div, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]

omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_kills_q_coeffs (D : Derivation ℤ L L) (a b ξS ξQ U V : L)
    (ha : D a = 0) (hb : D b = 0) (hξS : D ξS = 0) (hξQ : D ξQ = 0) (hU : D U = 0) (hV : D V = 0) :
    D (q1_a2 a b U V) = 0 ∧ D (q1_a1 a b ξS ξQ U V) = 0 ∧ D (q1_a0 ξS ξQ U V) = 0 ∧
    D (q2_b2 a b U V) = 0 ∧ D (q2_b1 a b ξS ξQ U V) = 0 ∧ D (q2_b0 ξS ξQ U V) = 0 := by
  have h0 : D (0 : L) = 0 := map_zero D
  have h1 : D (1 : L) = 0 := D.map_one_eq_zero
  have haS : D (a + ξS) = 0 := by rw [map_add, ha, hξS, add_zero]
  have hbQ : D (b + ξQ) = 0 := by rw [map_add, hb, hξQ, add_zero]
  refine ⟨D_kills_dH_dS D a b U V ha hb hU hV, ?_, D_kills_dH_dS D ξS ξQ U V hξS hξQ hU hV,
    D_kills_dH_dQ D a b 0 U V ha hb h0 hU hV, ?_, D_kills_dH_dQ D ξS ξQ 1 U V hξS hξQ h1 hU hV⟩
  · simp only [q1_a1, map_sub, D_kills_dH_dS D (a + ξS) (b + ξQ) U V haS hbQ hU hV,
      D_kills_dH_dS D a b U V ha hb hU hV, D_kills_dH_dS D ξS ξQ U V hξS hξQ hU hV, sub_zero]
  · simp only [q2_b1, map_add, map_sub, D.leibniz,
      D_kills_dH_dQ D (a + ξS) (b + ξQ) 0 U V haS hbQ h0 hU hV,
      D_kills_dH_dQ D a b 0 U V ha hb h0 hU hV,
      D_kills_dH_dQ D ξS ξQ 0 U V hξS hξQ h0 hU hV,
      D_ofNat_div, hb, hU, hV, smul_eq_mul, mul_zero, add_zero, sub_zero]

omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_kills_numM (D : Derivation ℤ L L) (mi : Fin 10) (a b ξS ξQ U V : L)
    (ha : D a = 0) (hb : D b = 0) (hξS : D ξS = 0) (hξQ : D ξQ = 0) (hU : D U = 0) (hV : D V = 0) :
    D (numM mi a b ξS ξQ U V) = 0 := by
  obtain ⟨ha2, ha1, ha0, hb2, hb1, hb0⟩ := D_kills_q_coeffs D a b ξS ξQ U V ha hb hξS hξQ hU hV
  fin_cases mi <;>
    simp only [numM, map_add, map_sub, D.leibniz, D.leibniz_pow, ha, hb, hξS, hξQ,
      ha2, ha1, ha0, hb2, hb1, hb0, D_ofNat, D_one_div,
      D.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, sub_zero]

omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_kills_weights (D : Derivation ℤ L L) (a b ξS ξQ U V : L)
    (ha : D a = 0) (hb : D b = 0) (hξS : D ξS = 0) (hξQ : D ξQ = 0) (hU : D U = 0) (hV : D V = 0) :
    D (A_0U a b ξS ξQ U V) = 0 ∧ D (A_0V a b ξS ξQ U V) = 0 ∧
    D (A_Y a b ξS ξQ U V) = 0 ∧ D (A_X a b ξS ξQ U V) = 0 ∧
    D ((S_ab_mat a b ξS ξQ U V).det) = 0 := by
  have hm (mi : Fin 10) : D (numM mi a b ξS ξQ U V) = 0 :=
    D_kills_numM D mi a b ξS ξQ U V ha hb hξS hξQ hU hV
  obtain ⟨ha2, ha1, ha0, hb2, hb1, hb0⟩ := D_kills_q_coeffs D a b ξS ξQ U V ha hb hξS hξQ hU hV
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [A_0U, map_add, map_sub, map_neg, D.leibniz, hm, D_ofNat, D_ofNat_div,
      smul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]
  · simp only [A_0V, map_add, map_sub, map_neg, D.leibniz, hm, D_ofNat, D_ofNat_div,
      smul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]
  · simp only [A_Y, map_add, map_sub, map_neg, D.leibniz, hm, hU, hV, D_ofNat, D_ofNat_div,
      smul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]
  · simp only [A_X, map_add, map_sub, map_neg, D.leibniz, hm, hU, D_ofNat, D_ofNat_div,
      smul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]
  · rw [Matrix.det_apply]
    rw [map_sum]
    apply Finset.sum_eq_zero; intro σ _
    rw [Units.smul_def, zsmul_eq_mul, D.leibniz, D.map_intCast, smul_zero, add_zero]
    suffices hprod : D (∏ i : Fin 4, S_ab_mat a b ξS ξQ U V (σ i) i) = 0 by rw [hprod, smul_zero]
    rw [Fin.prod_univ_four]
    have hent (r c : Fin 4) : D (S_ab_mat a b ξS ξQ U V r c) = 0 := by
      fin_cases r <;> fin_cases c <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, S_ab_mat,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          map_zero, ha2, ha1, ha0, hb2, hb1, hb0]
    simp only [D.leibniz, hent, smul_eq_mul, mul_zero, add_zero]


theorem sheet_horiz_identity (a b U V : L)
    (hE : ∀ k : Fin 4, E_fn k SL QL TL a b U V = 0)
    (hU0 : U ≠ 0) (hV0 : V ≠ 0) (hU1 : U ≠ 1) (hV1 : V ≠ 1)
    (hJ : (J_fib SL QL TL a b U V).det ≠ 0)
    (hM : (M_abSQ SL QL TL a b U V).det ≠ 0) :
    2 * ιL W2_K * ιL H0_K ^ 2 * resDivW_L (w_horiz a b U V) =
      -P18_of SL QL TL xL yL a b U V / (81 * (J_fib SL QL TL a b U V).det) := by
  let Jf := J_fib (SL (L := L)) QL TL a b U V
  let Mm := M_abSQ (SL (L := L)) QL TL a b U V
  let JS : L := δL 1 U * δL 2 V - δL 2 U * δL 1 V
  let JQ : L := δL 2 U * δL 0 V - δL 0 U * δL 2 V
  let JT : L := δL 0 U * δL 1 V - δL 1 U * δL 0 V
  have hJf_inj : ∀ v : Fin 4 → L, Jf.mulVec v = 0 → v = 0 := by
    intro v hv
    have hunit : IsUnit Jf.det := isUnit_iff_ne_zero.mpr hJ
    have hinv := Matrix.nonsing_inv_mul Jf hunit
    calc v = (1 : Matrix (Fin 4) (Fin 4) L).mulVec v := (Matrix.one_mulVec v).symm
      _ = (Jf⁻¹ * Jf).mulVec v := by rw [hinv]
      _ = Jf⁻¹.mulVec (Jf.mulVec v) := (Matrix.mulVec_mulVec v Jf⁻¹ Jf).symm
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  -- 1. δL 3 kills a, b, U, V!
  have hδ3_vec : Jf.mulVec ![δL 3 a, δL 3 b, δL 3 U, δL 3 V] = 0 := by
    ext k
    have hk := congrArg (δL (L := L) 3) (hE k)
    rw [map_zero, deriv_E_fn, δL_S, δL_Q, δL_T] at hk
    simp only [show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
      show (3 : Fin 4) ≠ 2 by decide, ↓reduceIte, mul_zero, zero_add] at hk
    simpa only [Jf, J_fib, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] using hk
  have hδ3_zero := hJf_inj _ hδ3_vec
  have hδ3_a : δL 3 a = 0 := congrFun hδ3_zero 0
  have hδ3_b : δL 3 b = 0 := congrFun hδ3_zero 1
  have hδ3_U : δL 3 U = 0 := congrFun hδ3_zero 2
  have hδ3_V : δL 3 V = 0 := congrFun hδ3_zero 3
  -- 2. Directional derivation D_line = a*δL 0 + b*δL 1 + δL 2 kills a, b, U, V, ξS, ξQ!
  let D_line : Derivation ℤ L L := a • δL 0 + b • δL 1 + δL 2
  have hD_line_apply (z : L) : D_line z = a * δL 0 z + b * δL 1 z + δL 2 z := by
    simp [D_line, smul_eq_mul]
  have hD_line_S : D_line SL = a := by rw [hD_line_apply, δL_S, δL_S, δL_S]; simp
  have hD_line_Q : D_line QL = b := by rw [hD_line_apply, δL_Q, δL_Q, δL_Q]; simp
  have hD_line_T : D_line TL = 1 := by rw [hD_line_apply, δL_T, δL_T, δL_T]; simp
  have hD_line_vec : Jf.mulVec ![D_line a, D_line b, D_line U, D_line V] = 0 := by
    ext k
    have hk := congrArg D_line (hE k)
    rw [map_zero, deriv_E_fn, hD_line_S, hD_line_Q, hD_line_T] at hk
    have hshift := line_shift_E k (SL (L := L)) QL TL a b U V
    have hshift0 : a * dE_dS k SL QL TL a b U V + b * dE_dQ k SL QL TL a b U V + dE_dT k SL QL TL a b U V = 0 := by
      rw [hshift]; fin_cases k <;> simp [hE]
    have hk' : dE_da k SL QL TL a b U V * D_line a + dE_db k SL QL TL a b U V * D_line b +
        dE_dU k SL QL TL a b U V * D_line U + dE_dV k SL QL TL a b U V * D_line V = 0 := by
      linear_combination hk - hshift0
    simpa only [Jf, J_fib, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] using hk'
  have hD_line_zero := hJf_inj _ hD_line_vec
  have hDl_a : D_line a = 0 := congrFun hD_line_zero 0
  have hDl_b : D_line b = 0 := congrFun hD_line_zero 1
  have hDl_U : D_line U = 0 := congrFun hD_line_zero 2
  have hDl_V : D_line V = 0 := congrFun hD_line_zero 3
  have hDl_ξS : D_line (SL - a * TL) = 0 := by
    rw [map_sub, D_line.leibniz, hD_line_S, hD_line_T, hDl_a]; simp [smul_eq_mul]
  have hDl_ξQ : D_line (QL - b * TL) = 0 := by
    rw [map_sub, D_line.leibniz, hD_line_Q, hD_line_T, hDl_b]; simp [smul_eq_mul]
  have hδ3_ξS : δL 3 (SL - a * TL) = 0 := by
    rw [map_sub, (δL 3).leibniz, δL_S, δL_T, hδ3_a]; simp [smul_eq_mul]
  have hδ3_ξQ : δL 3 (QL - b * TL) = 0 := by
    rw [map_sub, (δL 3).leibniz, δL_Q, δL_T, hδ3_b]; simp [smul_eq_mul]
  -- 3. Identities on (JS, JQ, JT): JS = a*JT, JQ = b*JT, div(J) = 0, δL 3 J = 0, JT = det(M)/det(J)!
  have hJS_eq : JS = a * JT := by
    dsimp only [JS, JT]
    rw [hD_line_apply] at hDl_U hDl_V
    linear_combination δL 1 U * hDl_V - δL 1 V * hDl_U
  have hJQ_eq : JQ = b * JT := by
    dsimp only [JQ, JT]
    rw [hD_line_apply] at hDl_U hDl_V
    linear_combination δL 0 V * hDl_U - δL 0 U * hDl_V
  have hJ_div : δL 0 JS + δL 1 JQ + δL 2 JT = 0 := by
    dsimp only [JS, JQ, JT]
    simp only [map_sub, (δL _).leibniz, smul_eq_mul]
    rw [δL_commute 0 1 U, δL_commute 0 2 U, δL_commute 1 2 U,
        δL_commute 0 1 V, δL_commute 0 2 V, δL_commute 1 2 V]
    ring
  have hJ_y : δL 3 JS = 0 ∧ δL 3 JQ = 0 ∧ δL 3 JT = 0 := by
    have hcommU (j : Fin 4) : δL 3 (δL j U) = 0 := by rw [δL_commute 3 j U, hδ3_U, map_zero]
    have hcommV (j : Fin 4) : δL 3 (δL j V) = 0 := by rw [δL_commute 3 j V, hδ3_V, map_zero]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [JS, JQ, JT, map_sub, (δL 3).leibniz, hcommU, hcommV, smul_eq_mul, mul_zero, add_zero, sub_zero]
  have hU_J : JS * δL 0 U + JQ * δL 1 U + JT * δL 2 U = 0 := by dsimp only [JS, JQ, JT]; ring
  have hV_J : JS * δL 0 V + JQ * δL 1 V + JT * δL 2 V = 0 := by dsimp only [JS, JQ, JT]; ring
  have hJT_eq : JT = Mm.det / Jf.det := by
    let B : Matrix (Fin 4) (Fin 4) L :=
      ![![1, 0, δL 0 a, δL 1 a],
        ![0, 1, δL 0 b, δL 1 b],
        ![0, 0, δL 0 U, δL 1 U],
        ![0, 0, δL 0 V, δL 1 V]]
    let Mm_neg : Matrix (Fin 4) (Fin 4) L :=
      fun k j => match j with
        | 0 => dE_da k SL QL TL a b U V
        | 1 => dE_db k SL QL TL a b U V
        | 2 => -dE_dS k SL QL TL a b U V
        | 3 => -dE_dQ k SL QL TL a b U V
    have hprod : Jf * B = Mm_neg := by
      ext k j
      rw [Matrix.mul_apply, Fin.sum_univ_four]
      have hk0 := congrArg (δL (L := L) 0) (hE k)
      rw [map_zero, deriv_E_fn, δL_S, δL_Q, δL_T] at hk0
      simp only [↓reduceIte, show (0 : Fin 4) ≠ 1 by decide, show (0 : Fin 4) ≠ 2 by decide,
        mul_one, mul_zero, add_zero] at hk0
      have hk1 := congrArg (δL (L := L) 1) (hE k)
      rw [map_zero, deriv_E_fn, δL_S, δL_Q, δL_T] at hk1
      simp only [↓reduceIte, show (1 : Fin 4) ≠ 0 by decide, show (1 : Fin 4) ≠ 2 by decide,
        mul_one, mul_zero, zero_add, add_zero] at hk1
      fin_cases j
      · simp only [Fin.zero_eta, Jf, J_fib, B, Mm_neg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
      · simp only [Fin.mk_one, Jf, J_fib, B, Mm_neg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
      · simp only [Fin.reduceFinMk, Jf, J_fib, B, Mm_neg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        linear_combination hk0
      · simp only [Fin.reduceFinMk, Jf, J_fib, B, Mm_neg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        linear_combination hk1
    have hdetB : B.det = JT := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_four]
      let B1 : Matrix (Fin 3) (Fin 3) L :=
        ![![1, δL 0 b, δL 1 b], ![0, δL 0 U, δL 1 U], ![0, δL 0 V, δL 1 V]]
      have hsub1 : B.submatrix (Fin.succAbove 0) Fin.succ = B1 := by
        ext i j; fin_cases i <;> fin_cases j <;> rfl
      rw [hsub1, Matrix.det_succ_column_zero, Fin.sum_univ_three]
      let B2 : Matrix (Fin 2) (Fin 2) L := ![![δL 0 U, δL 1 U], ![δL 0 V, δL 1 V]]
      have hsub2 : B1.submatrix (Fin.succAbove 0) Fin.succ = B2 := by
        ext i j; fin_cases i <;> fin_cases j <;> rfl
      rw [hsub2]
      have hB2 : B2.det = JT := by rw [Matrix.det_fin_two]; simp [B2, JT]
      simp [B, B1, hB2]
    have hdetM : Mm_neg.det = Mm.det := by
      let Sgn : Matrix (Fin 4) (Fin 4) L := Matrix.diagonal ![1, 1, -1, -1]
      have hEq : Mm_neg = Mm * Sgn := by
        ext k j; fin_cases j <;> simp [Mm_neg, Mm, M_abSQ, Sgn, Matrix.mul_diagonal]
      rw [hEq, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_four]
      simp
    have hdet := congrArg Matrix.det hprod
    rw [Matrix.det_mul, hdetB, hdetM] at hdet
    exact (eq_div_iff hJ).mpr (by rw [mul_comm]; exact hdet)
  -- 4. Automatic G ≠ 0 from W_G_ne_zero and u ≠ 0!
  have hu_ne : u_of U ≠ 0 := by
    rw [u_of]; exact div_ne_zero (sub_ne_zero.mpr hU1) (by norm_num)
  have hv_ne : v_of V ≠ 0 := by
    rw [v_of]; exact div_ne_zero (sub_ne_zero.mpr hV1) (by norm_num)
  have hG_ne : G_of SL QL TL xL yL U V ≠ 0 := by
    intro hG0
    have hG_eq : u_of U * ιL DX2_K + v_of V * ιL DY2_K = 0 := by
      simpa only [G_of, DX2_of_L, DY2_of_L] using hG0
    have hδ3_u : δL 3 (u_of U) = 0 := by
      rw [u_of, D_div _ _ _ (by norm_num : (9 : L) ≠ 0), map_sub, hδ3_U, (δL 3).map_one_eq_zero, D_ofNat]; simp
    have hδ3_v : δL 3 (v_of V) = 0 := by
      rw [v_of, D_div _ _ _ (by norm_num : (9 : L) ≠ 0), map_sub, hδ3_V, (δL 3).map_one_eq_zero, D_ofNat]; simp
    have hdG0 := congrArg (δL (L := L) 3) hG_eq
    rw [map_zero, map_add, (δL 3).leibniz, (δL 3).leibniz, hδ3_u, hδ3_v, δL_apply, δL_apply] at hdG0
    simp only [smul_eq_mul, mul_zero, add_zero] at hdG0
    have hWG : u_of U * ιL (DX2_K * δ 3 DY2_K - DY2_K * δ 3 DX2_K) = 0 := by
      simp only [map_sub, map_mul]
      linear_combination ιL (δ 3 DY2_K) * hG_eq - ιL DY2_K * hdG0
    have hWG_ne : ιL (L := L) (DX2_K * δ 3 DY2_K - DY2_K * δ 3 DX2_K) ≠ 0 :=
      (map_ne_zero_iff ιL ιL.injective).mpr W_G_ne_zero
    exact mul_ne_zero hu_ne hWG_ne hWG
  -- 5. Compute resDivW_L of the 3 primitive vectors alY, alX, al0!
  let G := G_of (SL (L := L)) QL TL xL yL U V
  let H0 := H0_of (SL (L := L)) QL TL
  have hH0_eq : H0 = ιL H0_K := H0_of_L
  have hH0_ne : H0 ≠ 0 := by rw [hH0_eq]; exact H0L_ne
  let alY : Fin 5 → L := fun k => PhiY_fn k SL QL TL xL yL U V / G
  let alX : Fin 5 → L := fun k => PhiX_fn k SL QL TL xL yL U V / G
  let al0 : Fin 5 → L := fun k => (A1_of SL QL U V / H0) * alY k + (B1_of TL U V / H0) * alX k
  obtain ⟨hCY_cancel, hCX_cancel⟩ := G_sq_cancellation SL QL TL xL yL a b U V F5_of_L (hE 0) (hE 1) hU0 hV0
  have hG_ne' : G ≠ 0 := hG_ne
  have hW2_ne : ιL (L := L) W2_K ≠ 0 := W2L_ne
  have hrY : resDivW_L (w_of_1form alY JS JQ JT) =
      -(dot_ab (QY_num SL QL TL xL yL U V) a b / v_of V) * JT / (2 * ιL W2_K) := by
    rw [resDivW_L_PhiY_div_G U V JS JQ JT hG_ne hJ_div hJ_y hU_J hV_J hδ3_U hδ3_V, hJS_eq, hJQ_eq]
    have hdot : CY_of SL QL TL xL yL U V 0 * (a * JT) + CY_of SL QL TL xL yL U V 1 * (b * JT) +
        CY_of SL QL TL xL yL U V 2 * JT = dot_ab (CY_of SL QL TL xL yL U V) a b * JT := by
      simp only [dot_ab]; ring
    rw [hdot]
    have h2W2 : (2 * ιL (L := L) W2_K) ≠ 0 := mul_ne_zero (by norm_num) hW2_ne
    have hG2 : G ^ 2 ≠ 0 := pow_ne_zero 2 hG_ne'
    field_simp [h2W2, hW2_ne, hG2, hG_ne, hG_ne', hv_ne]
    linear_combination -JT * hCY_cancel
  have hrX : resDivW_L (w_of_1form alX JS JQ JT) =
      -(dot_ab (QX_num SL QL TL xL yL U V) a b / u_of U) * JT / (2 * ιL W2_K) := by
    rw [resDivW_L_PhiX_div_G U V JS JQ JT hG_ne hJ_div hJ_y hU_J hV_J hδ3_U hδ3_V, hJS_eq, hJQ_eq]
    have hdot : CX_of SL QL TL xL yL U V 0 * (a * JT) + CX_of SL QL TL xL yL U V 1 * (b * JT) +
        CX_of SL QL TL xL yL U V 2 * JT = dot_ab (CX_of SL QL TL xL yL U V) a b * JT := by
      simp only [dot_ab]; ring
    rw [hdot]
    have h2W2 : (2 * ιL (L := L) W2_K) ≠ 0 := mul_ne_zero (by norm_num) hW2_ne
    have hG2 : G ^ 2 ≠ 0 := pow_ne_zero 2 hG_ne'
    field_simp [h2W2, hW2_ne, hG2, hG_ne, hG_ne', hu_ne]
    linear_combination -JT * hCX_cancel
  have hr0 : resDivW_L (w_of_1form al0 JS JQ JT) =
      (A1_of SL QL U V / H0) * resDivW_L (w_of_1form alY JS JQ JT) +
      (B1_of TL U V / H0) * resDivW_L (w_of_1form alX JS JQ JT) -
      (cA1_of SL QL TL a b U V * JT / (H0 ^ 2 * v_of V)) * EB_of SL QL TL xL yL U V / (2 * ιL W2_K) := by
    have hw0 : w_of_1form al0 JS JQ JT = fun i =>
        (A1_of SL QL U V / H0) * w_of_1form alY JS JQ JT i +
        (B1_of TL U V / H0) * w_of_1form alX JS JQ JT i := by
      funext i
      rw [show al0 = fun k => (A1_of SL QL U V / H0) * alY k + (B1_of TL U V / H0) * alX k from rfl,
        w_of_1form_add, w_of_1form_smul, w_of_1form_smul]
    rw [hw0, resDivW_L_add, resDivW_L_smul, resDivW_L_smul]
    -- δL 3 kills A1/H0 and B1/H0!
    have hδ3_H0 : δL 3 H0 = 0 := by
      simp only [H0, H0_of, map_add, map_sub, map_neg, (δL 3).leibniz, (δL 3).leibniz_pow,
        δL_S, δL_Q, δL_T, D_ofNat, D_ofNat_div, smul_eq_mul, nsmul_eq_mul]; simp
    have hδ3_A1 : δL 3 (A1_of SL QL U V) = 0 := by
      simp only [A1_of, map_sub, (δL 3).leibniz, (δL 3).leibniz_pow, δL_S, δL_Q, hδ3_U, hδ3_V,
        D_ofNat, D_one_div, smul_eq_mul, nsmul_eq_mul]; simp
    have hδ3_B1 : δL 3 (B1_of TL U V) = 0 := by
      simp only [B1_of, map_sub, (δL 3).leibniz, (δL 3).leibniz_pow, δL_T, hδ3_U, hδ3_V,
        D_ofNat, D_one_div, smul_eq_mul, nsmul_eq_mul]; simp
    have hδ3_AH : δL 3 (A1_of SL QL U V / H0) = 0 := by
      rw [D_div _ _ _ hH0_ne, hδ3_A1, hδ3_H0]; simp
    have hδ3_BH : δL 3 (B1_of TL U V / H0) = 0 := by
      rw [D_div _ _ _ hH0_ne, hδ3_B1, hδ3_H0]; simp
    -- D_line of A1/H0 and B1/H0!
    have hDl_H0 : D_line H0 = dH0_fn 0 SL QL TL * a + dH0_fn 1 SL QL TL * b + dH0_fn 2 SL QL TL := by
      simp only [H0, H0_of, dH0_fn, map_add, map_sub, map_neg, D_line.leibniz, D_line.leibniz_pow,
        hD_line_S, hD_line_Q, hD_line_T, D_ofNat, D_ofNat_div,
        smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
      norm_num only; ring
    have hDl_A1 : D_line (A1_of SL QL U V) = dA1_fn 0 SL QL U V * a + dA1_fn 1 SL QL U V * b + dA1_fn 2 SL QL U V := by
      simp only [A1_of, dA1_fn, map_sub, D_line.leibniz, D_line.leibniz_pow,
        hD_line_S, hD_line_Q, hDl_U, hDl_V, D_ofNat, D_one_div,
        smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
      norm_num only; ring
    have hDl_AH : D_line (A1_of SL QL U V / H0) = cA1_of SL QL TL a b U V / H0 ^ 2 := by
      rw [D_div _ _ _ hH0_ne, hDl_A1, hDl_H0, cA1_of]
      dsimp only [H0]; ring
    have hDl_uB : u_of U * D_line (A1_of SL QL U V / H0) + v_of V * D_line (B1_of TL U V / H0) = 0 := by
      have h0 := H_cub_eq_H0_A1_B1 (SL (L := L)) QL TL U V
      change E_fn 0 SL QL TL a b U V = _ at h0
      rw [hE 0] at h0
      have hdiv : u_of U * (A1_of SL QL U V / H0) + v_of V * (B1_of TL U V / H0) = -(U * V) := by
        apply mul_right_cancel₀ hH0_ne
        field_simp [hH0_ne]; linear_combination -h0
      have hDl_u : D_line (u_of U) = 0 := by
        rw [u_of, D_div _ _ _ (by norm_num : (9 : L) ≠ 0), map_sub, hDl_U, D_line.map_one_eq_zero, D_ofNat]; simp
      have hDl_v : D_line (v_of V) = 0 := by
        rw [v_of, D_div _ _ _ (by norm_num : (9 : L) ≠ 0), map_sub, hDl_V, D_line.map_one_eq_zero, D_ofNat]; simp
      have hd := congrArg D_line hdiv
      rw [map_add, D_line.leibniz, D_line.leibniz, map_neg, D_line.leibniz, hDl_u, hDl_v, hDl_U, hDl_V] at hd
      simpa only [smul_eq_mul, mul_zero, zero_add, add_zero, neg_zero] using hd
    -- Compute the two Fin 4 derivative sums!
    have hsum_y : (∑ i : Fin 4, δL i (A1_of SL QL U V / H0) * w_of_1form alY JS JQ JT i) +
        (∑ i : Fin 4, δL i (B1_of TL U V / H0) * w_of_1form alX JS JQ JT i) =
        -(cA1_of SL QL TL a b U V * JT / (H0 ^ 2 * v_of V)) * EB_of SL QL TL xL yL U V / (2 * ιL W2_K) := by
      rw [Fin.sum_univ_four, Fin.sum_univ_four]
      simp only [w_of_1form, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        hδ3_AH, hδ3_BH, zero_mul, add_zero, hJS_eq, hJQ_eq]
      have hD1 : δL 0 (A1_of SL QL U V / H0) * (a * JT) + δL 1 (A1_of SL QL U V / H0) * (b * JT) +
          δL 2 (A1_of SL QL U V / H0) * JT = D_line (A1_of SL QL U V / H0) * JT := by
        rw [hD_line_apply]; ring
      have hD2 : δL 0 (B1_of TL U V / H0) * (a * JT) + δL 1 (B1_of TL U V / H0) * (b * JT) +
          δL 2 (B1_of TL U V / H0) * JT = D_line (B1_of TL U V / H0) * JT := by
        rw [hD_line_apply]; ring
      have hfact :
          (δL 0 (A1_of SL QL U V / H0) * ((dF5_fn 3 SL QL TL xL yL * alY 4 - dF5_fn 4 SL QL TL xL yL * alY 3) * (a * JT)) +
           δL 1 (A1_of SL QL U V / H0) * ((dF5_fn 3 SL QL TL xL yL * alY 4 - dF5_fn 4 SL QL TL xL yL * alY 3) * (b * JT)) +
           δL 2 (A1_of SL QL U V / H0) * ((dF5_fn 3 SL QL TL xL yL * alY 4 - dF5_fn 4 SL QL TL xL yL * alY 3) * JT)) +
          (δL 0 (B1_of TL U V / H0) * ((dF5_fn 3 SL QL TL xL yL * alX 4 - dF5_fn 4 SL QL TL xL yL * alX 3) * (a * JT)) +
           δL 1 (B1_of TL U V / H0) * ((dF5_fn 3 SL QL TL xL yL * alX 4 - dF5_fn 4 SL QL TL xL yL * alX 3) * (b * JT)) +
           δL 2 (B1_of TL U V / H0) * ((dF5_fn 3 SL QL TL xL yL * alX 4 - dF5_fn 4 SL QL TL xL yL * alX 3) * JT)) =
          (D_line (A1_of SL QL U V / H0) * DY2_of TL yL - D_line (B1_of TL U V / H0) * DX2_of SL QL xL) / G *
            JT * (dF5_fn 3 SL QL TL xL yL * br_fn 4 SL QL TL xL yL U V -
                  dF5_fn 4 SL QL TL xL yL * br_fn 3 SL QL TL xL yL U V) := by
        have hcyY : dF5_fn 3 SL QL TL xL yL * alY 4 - dF5_fn 4 SL QL TL xL yL * alY 3 =
            (DY2_of TL yL / G) * (dF5_fn 3 SL QL TL xL yL * br_fn 4 SL QL TL xL yL U V -
              dF5_fn 4 SL QL TL xL yL * br_fn 3 SL QL TL xL yL U V) := by
          dsimp only [alY, PhiY_fn]; ring
        have hcyX : dF5_fn 3 SL QL TL xL yL * alX 4 - dF5_fn 4 SL QL TL xL yL * alX 3 =
            -(DX2_of SL QL xL / G) * (dF5_fn 3 SL QL TL xL yL * br_fn 4 SL QL TL xL yL U V -
              dF5_fn 4 SL QL TL xL yL * br_fn 3 SL QL TL xL yL U V) := by
          dsimp only [alX, PhiX_fn]; ring
        rw [hcyY, hcyX]
        linear_combination
          (DY2_of TL yL / G) * (dF5_fn 3 SL QL TL xL yL * br_fn 4 SL QL TL xL yL U V -
            dF5_fn 4 SL QL TL xL yL * br_fn 3 SL QL TL xL yL U V) * hD1 -
          (DX2_of SL QL xL / G) * (dF5_fn 3 SL QL TL xL yL * br_fn 4 SL QL TL xL yL U V -
            dF5_fn 4 SL QL TL xL yL * br_fn 3 SL QL TL xL yL U V) * hD2
      rw [hfact]
      have hG_cancel : (D_line (A1_of SL QL U V / H0) * DY2_of TL yL -
          D_line (B1_of TL U V / H0) * DX2_of SL QL xL) / G =
          D_line (A1_of SL QL U V / H0) / v_of V := by
        have hGv : v_of V * (D_line (A1_of SL QL U V / H0) * DY2_of TL yL -
            D_line (B1_of TL U V / H0) * DX2_of SL QL xL) =
            D_line (A1_of SL QL U V / H0) * G := by
          dsimp only [G, G_of]
          linear_combination -DX2_of SL QL xL * hDl_uB
        field_simp [hG_ne', hv_ne]; linear_combination hGv
      rw [hG_cancel, hDl_AH, EB_of, W2_of_L]
      have h2W2 : (2 * ιL (L := L) W2_K) ≠ 0 := mul_ne_zero (by norm_num) hW2_ne
      field_simp [h2W2, hW2_ne, hH0_ne, hv_ne]; ring
    linear_combination hsum_y
  -- 6. Scalar factors f0, fY, fX are killed by both δL 3 and D_line!
  let ξS : L := SL - a * TL
  let ξQ : L := QL - b * TL
  let dM : L := Mm.det
  have hdM_eq : dM = (S_ab_mat a b ξS ξQ U V).det := M_abSQ_det SL QL TL a b U V
  have hdM_ne : dM ≠ 0 := hM
  have h81dM : (81 * dM : L) ≠ 0 := mul_ne_zero (by norm_num) hdM_ne
  obtain ⟨hDl_0U, hDl_0V, hDl_Y, hDl_X, hDl_S⟩ :=
    D_kills_weights D_line a b ξS ξQ U V hDl_a hDl_b hDl_ξS hDl_ξQ hDl_U hDl_V
  obtain ⟨h3_0U, h3_0V, h3_Y, h3_X, h3_S⟩ :=
    D_kills_weights (δL 3) a b ξS ξQ U V hδ3_a hδ3_b hδ3_ξS hδ3_ξQ hδ3_U hδ3_V
  have hDl_dM : D_line dM = 0 := by rw [hdM_eq]; exact hDl_S
  have h3_dM : δL 3 dM = 0 := by rw [hdM_eq]; exact h3_S
  let f0 : L := (A_0U a b ξS ξQ U V / U + A_0V a b ξS ξQ U V / V) / (81 * dM)
  let fY : L := A_Y a b ξS ξQ U V / (81 * dM)
  let fX : L := A_X a b ξS ξQ U V / (81 * dM)
  have hD_kill_f (D : Derivation ℤ L L) (h0U : D (A_0U a b ξS ξQ U V) = 0)
      (h0V : D (A_0V a b ξS ξQ U V) = 0) (hY : D (A_Y a b ξS ξQ U V) = 0)
      (hX : D (A_X a b ξS ξQ U V) = 0) (hU : D U = 0) (hV : D V = 0) (hdM : D dM = 0) :
      D f0 = 0 ∧ D fY = 0 ∧ D fX = 0 := by
    have h81 : D (81 * dM) = 0 := by rw [D.leibniz, D_ofNat, hdM]; simp [smul_eq_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [show f0 = (A_0U a b ξS ξQ U V / U + A_0V a b ξS ξQ U V / V) / (81 * dM) from rfl,
        D_div _ _ _ h81dM, map_add, D_div _ _ _ hU0, D_div _ _ _ hV0, h0U, h0V, hU, hV, h81]; simp
    · rw [show fY = A_Y a b ξS ξQ U V / (81 * dM) from rfl, D_div _ _ _ h81dM, hY, h81]; simp
    · rw [show fX = A_X a b ξS ξQ U V / (81 * dM) from rfl, D_div _ _ _ h81dM, hX, h81]; simp
  obtain ⟨hDl_f0, hDl_fY, hDl_fX⟩ := hD_kill_f D_line hDl_0U hDl_0V hDl_Y hDl_X hDl_U hDl_V hDl_dM
  obtain ⟨h3_f0, h3_fY, h3_fX⟩ := hD_kill_f (δL 3) h3_0U h3_0V h3_Y h3_X hδ3_U hδ3_V h3_dM
  have hkill_smul (f : L) (α : Fin 5 → L) (h3f : δL 3 f = 0) (hDlf : D_line f = 0) :
      resDivW_L (fun i => f * w_of_1form α JS JQ JT i) = f * resDivW_L (w_of_1form α JS JQ JT) := by
    rw [resDivW_L_smul]
    suffices h0 : ∑ i : Fin 4, δL i f * w_of_1form α JS JQ JT i = 0 by rw [h0, add_zero]
    rw [Fin.sum_univ_four]
    simp only [w_of_1form, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      h3f, zero_mul, add_zero, hJS_eq, hJQ_eq]
    rw [hD_line_apply] at hDlf
    linear_combination (dF5_fn 3 SL QL TL xL yL * α 4 - dF5_fn 4 SL QL TL xL yL * α 3) * JT * hDlf
  -- 7. Assemble everything and cancel dM!
  have hw_eq : w_horiz a b U V = fun i =>
      f0 * w_of_1form al0 JS JQ JT i + fY * w_of_1form alY JS JQ JT i + fX * w_of_1form alX JS JQ JT i := rfl
  rw [hw_eq, resDivW_L_add, resDivW_L_add,
      hkill_smul f0 al0 h3_f0 hDl_f0, hkill_smul fY alY h3_fY hDl_fY, hkill_smul fX alX h3_fX hDl_fX,
      hr0, hrY, hrX, hJT_eq, ← hH0_eq]
  dsimp only [f0, fY, fX, dM, P18_of]
  have h2W2 : (2 * ιL (L := L) W2_K) ≠ 0 := mul_ne_zero (by norm_num) hW2_ne
  have h81 : (81 : L) ≠ 0 := by norm_num
  have hMm_ne : Mm.det ≠ 0 := hM
  have hJf_ne : Jf.det ≠ 0 := hJ
  have hH0_ne' : H0_of (SL (L := L)) QL TL ≠ 0 := hH0_ne
  change 2 * ιL W2_K * H0_of SL QL TL ^ 2 * _ =
    -_ / (81 * Jf.det)
  dsimp only [H0]
  generalize A_0U a b ξS ξQ U V = g0U; generalize A_0V a b ξS ξQ U V = g0V
  generalize A_Y a b ξS ξQ U V = gY; generalize A_X a b ξS ξQ U V = gX
  generalize dot_ab (QY_num SL QL TL xL yL U V) a b = qYn
  generalize dot_ab (QX_num SL QL TL xL yL U V) a b = qXn
  generalize A1_of SL QL U V = a1; generalize B1_of TL U V = b1
  generalize cA1_of SL QL TL a b U V = ca1; generalize EB_of SL QL TL xL yL U V = eb
  generalize H0_of (SL (L := L)) QL TL = h0 at hH0_ne' ⊢
  generalize Mm.det = dm at hMm_ne ⊢; generalize Jf.det = dj at hJf_ne ⊢
  generalize ιL (L := L) W2_K = w2 at h2W2 hW2_ne ⊢
  generalize u_of U = uu at hu_ne ⊢; generalize v_of V = vv at hv_ne ⊢
  field_simp [h2W2, hW2_ne, hH0_ne', hMm_ne, hJf_ne, hU0, hV0, hu_ne, hv_ne, h81]
  ring

end SheetL

end SymmetricSexticResidual.SheetCalculus


theorem solution
    {L : Type*} [Field L] [CharZero L] [Algebra SymmetricSexticResidual.K5Field.K5 L]
    [FiniteDimensional SymmetricSexticResidual.K5Field.K5 L]
    (a b U V : L)
    (hE : ∀ k : Fin 4, SymmetricSexticResidual.SheetCalculus.E_fn k
      (SymmetricSexticResidual.SheetCalculus.SL (L := L))
      SymmetricSexticResidual.SheetCalculus.QL
      SymmetricSexticResidual.SheetCalculus.TL a b U V = 0)
    (hU0 : U ≠ 0) (hV0 : V ≠ 0) (hU1 : U ≠ 1) (hV1 : V ≠ 1)
    (hJ : (SymmetricSexticResidual.SheetCalculus.J_fib
      (SymmetricSexticResidual.SheetCalculus.SL (L := L))
      SymmetricSexticResidual.SheetCalculus.QL
      SymmetricSexticResidual.SheetCalculus.TL a b U V).det ≠ 0)
    (hM : (SymmetricSexticResidual.SheetCalculus.M_abSQ
      (SymmetricSexticResidual.SheetCalculus.SL (L := L))
      SymmetricSexticResidual.SheetCalculus.QL
      SymmetricSexticResidual.SheetCalculus.TL a b U V).det ≠ 0) :
    2 * SymmetricSexticResidual.SheetCalculus.ιL SymmetricSexticResidual.K5Field.W2_K *
      SymmetricSexticResidual.SheetCalculus.ιL SymmetricSexticResidual.K5Field.H0_K ^ 2 *
      SymmetricSexticResidual.SheetCalculus.resDivW_L (SymmetricSexticResidual.SheetCalculus.w_horiz a b U V) =
      -SymmetricSexticResidual.SheetCalculus.P18_of
        (SymmetricSexticResidual.SheetCalculus.SL (L := L))
        SymmetricSexticResidual.SheetCalculus.QL
        SymmetricSexticResidual.SheetCalculus.TL
        SymmetricSexticResidual.SheetCalculus.xL
        SymmetricSexticResidual.SheetCalculus.yL a b U V /
      (81 * (SymmetricSexticResidual.SheetCalculus.J_fib
        (SymmetricSexticResidual.SheetCalculus.SL (L := L))
        SymmetricSexticResidual.SheetCalculus.QL
        SymmetricSexticResidual.SheetCalculus.TL a b U V).det) :=
  SymmetricSexticResidual.SheetCalculus.sheet_horiz_identity a b U V hE hU0 hV0 hU1 hV1 hJ hM
