-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.regularAt_eta_L_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T09:31:52.521794+00:00
-- url     : https://prove2.me/submissions/a415f9c9-ed42-43db-a1a3-3e9e4d0fc8d1

import Definitions.Def_HodgeComputerFormal_CoverResidues
import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_CoverFactors
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_reg_identities
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.CoverResidue
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators Matrix Classical

private abbrev nine_U_G_AC_eq := HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.nine_U_G_AC
private abbrev pnm_P_G_eval_one := @HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.pnm_P_G_one
private abbrev P18_z_AC_eq_regX := HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.P18_regX
private abbrev P18_z_AC_eq_regY := HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.P18_regY
private abbrev eta_AC_eq_a_elim := HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.eta_a_elim

/-- Any root in a finite extension `L / K5` of a nonzero polynomial over `K5` whose coefficients
are killed by `δ 3` is itself killed by `δL 3`. -/
lemma δL3_eq_zero_of_isRoot {L : Type*} [Field L] [Algebra K5 L] [FiniteDimensional K5 L]
    (P : K5[X]) (hP : P ≠ 0) (hδ : ∀ k : ℕ, δ 3 (P.coeff k) = 0)
    (r : L) (hr : (P.map (algebraMap K5 L)).eval r = 0) :
    δL (L := L) 3 r = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  let _ : Algebra ℤ L := Ring.toIntAlgebra L
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    have hdeg_pos : 0 < P.natDegree := by
      by_contra h0; push Not at h0
      have hC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp h0)
      rw [hC, Polynomial.map_C, Polynomial.eval_C] at hr
      have hc0 : P.coeff 0 = 0 := (algebraMap K5 L).injective (by simpa using hr)
      exact hP (by rw [hC, hc0, map_zero])
    have hev_deriv : δL (L := L) 3 ((P.map (algebraMap K5 L)).eval r) =
        (P.derivative.map (algebraMap K5 L)).eval r * δL (L := L) 3 r := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le),
        map_sum]
      have hterm (k : ℕ) :
          δL (L := L) 3 ((P.map (algebraMap K5 L)).coeff k * r ^ k) =
            (algebraMap K5 L) ((k : K5) * P.coeff k) * r ^ (k - 1) * δL (L := L) 3 r := by
        rw [Polynomial.coeff_map, (δL (L := L) 3).leibniz, δL_apply, hδ k, map_zero,
          smul_eq_mul, smul_eq_mul, mul_zero, add_zero, (δL (L := L) 3).leibniz_pow,
          smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
        ring
      simp_rw [hterm]
      rw [Nat.succ_eq_add_one, Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, map_zero, add_zero, Nat.add_sub_cancel]
      rw [← Finset.sum_mul]
      congr 1
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_of_le_of_lt Polynomial.natDegree_map_le
        (Polynomial.natDegree_derivative_lt (by omega : P.natDegree ≠ 0)))]
      apply Finset.sum_congr rfl; intro k _
      rw [Polynomial.coeff_map, Polynomial.coeff_derivative]
      simp only [Nat.cast_add, Nat.cast_one, map_mul, map_add, map_natCast, map_one]
      ring
    rw [hr, map_zero] at hev_deriv
    by_cases hPd : (P.derivative.map (algebraMap K5 L)).eval r = 0
    · have hPd_ne : P.derivative ≠ 0 := by
        intro h0
        have hc := congrArg (fun f : K5[X] => f.coeff (P.natDegree - 1)) h0
        rw [Polynomial.coeff_zero, Polynomial.coeff_derivative, Nat.sub_add_cancel hdeg_pos] at hc
        have hlc : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
        have hnat : ((P.natDegree : K5)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hc' : P.coeff P.natDegree * (P.natDegree : K5) = 0 := by
          simpa [Nat.cast_sub hdeg_pos] using hc
        exact mul_ne_zero hlc hnat hc'
      have hδd : ∀ k : ℕ, δ 3 (P.derivative.coeff k) = 0 := by
        intro k
        rw [Polynomial.coeff_derivative, (δ 3).leibniz, hδ (k + 1), smul_eq_mul, smul_eq_mul,
          mul_zero, add_zero]
        have hnat : δ 3 ((k : K5) + 1) = 0 := by
          rw [map_add, (δ 3).map_natCast, (δ 3).map_one_eq_zero, add_zero]
        rw [hnat, mul_zero]
      exact ih P.derivative.natDegree (by rw [← hd]; exact Polynomial.natDegree_derivative_lt (by omega))
        P.derivative hPd_ne hδd hPd rfl
    · exact (mul_eq_zero.mp hev_deriv.symm).resolve_left hPd


section RegACProof
variable {L : Type} [Field L] [Algebra K5 L]
private lemma regAt_toRat (r : L) (P : K5[X]) : RegAt r (toRat P) := by
  rw [RegAt, mapRatFunc_algebraMap]; exact RegularAt.polynomial r _

private lemma valAt_toRat (r : L) (P : K5[X]) :
    valAt r (toRat P) = (P.map (algebraMap K5 L)).eval r := by
  rw [valAt, mapRatFunc_algebraMap, valueAt_polynomial]

private lemma regUnitAt_toRat {r : L} {P : K5[X]}
    (hP : (P.map (algebraMap K5 L)).eval r ≠ 0) : RegUnitAt r (toRat P) :=
  ⟨regAt_toRat r P, by rwa [valAt_toRat]⟩

private lemma regAt_add {r : L} {f g : RatFunc K5} (hf : RegAt r f) (hg : RegAt r g) :
    RegAt r (f + g) := by rw [RegAt, map_add]; exact hf.add hg
private lemma regAt_sub {r : L} {f g : RatFunc K5} (hf : RegAt r f) (hg : RegAt r g) :
    RegAt r (f - g) := by rw [RegAt, map_sub]; exact regAt_sub_local hf hg
private lemma regAt_neg {r : L} {f : RatFunc K5} (hf : RegAt r f) :
    RegAt r (-f) := by rw [RegAt, map_neg]; exact regAt_neg_local hf
private lemma regAt_mul {r : L} {f g : RatFunc K5} (hf : RegAt r f) (hg : RegAt r g) :
    RegAt r (f * g) := by rw [RegAt, map_mul]; exact regAt_mul_local hf hg
private lemma regAt_div {r : L} {f g : RatFunc K5} (hf : RegAt r f) (hg : RegUnitAt r g) :
    RegAt r (f / g) := by rw [RegAt, map_div₀]; exact regAt_div_of_valueAt_ne hf hg.1 hg.2
private lemma regAt_inv {r : L} {g : RatFunc K5} (hg : RegUnitAt r g) :
    RegAt r g⁻¹ := by rw [RegAt, map_inv₀]; exact regAt_inv_of_valueAt_ne hg.1 hg.2

private lemma regAC_evalAC {r : L} {p : PairAlg (RatFunc K5)}
    (h0 : RegAt r p.c0) (h1 : RegAt r p.c1) : RegAC r (evalAC p) :=
  ⟨by rw [coordsAC_evalAC]; exact h0, by rw [coordsAC_evalAC]; exact h1⟩

private lemma regAC_ιC_rat {r : L} {g : RatFunc K5} (hg : RegAt r g) : RegAC r (ιC_rat g) := by
  rw [← evalAC_ofScalar]
  exact regAC_evalAC hg (by dsimp only [PairAlg.ofScalar]; rw [← map_zero toRat]; exact regAt_toRat r 0)

private lemma regAC_polyC (r : L) (P : K5[X]) : RegAC r (polyC P) :=
  regAC_ιC_rat (regAt_toRat r P)

private lemma regAC_pairC (r : L) (x : PairAlg K5[X]) : RegAC r (pairC x) :=
  regAC_evalAC (regAt_toRat r x.c0) (regAt_toRat r x.c1)

private lemma regAC_ιC_K5 (r : L) (c : K5) : RegAC r (ιC_K5 c) := by
  have : ιC_K5 c = polyC (C c) := by simp [ιC_K5, polyC, RatFunc.algebraMap_C]
  rw [this]; exact regAC_polyC r (C c)

private lemma regAC_zero (r : L) : RegAC r 0 := by
  have : (0 : A_C) = polyC 0 := by simp [polyC]
  rw [this]; exact regAC_polyC r 0
private lemma regAC_one (r : L) : RegAC r 1 := by
  have : (1 : A_C) = polyC 1 := by simp [polyC]
  rw [this]; exact regAC_polyC r 1
private lemma regAC_ofNat (r : L) (n : ℕ) [n.AtLeastTwo] : RegAC r (OfNat.ofNat n) := by
  have : (OfNat.ofNat n : A_C) = polyC (C (OfNat.ofNat n)) := by
    simp [polyC, map_ofNat]
  rw [this]; exact regAC_polyC r _
private lemma regAC_W_C (r : L) : RegAC r W_C := by
  rw [← evalAC_W]
  exact regAC_evalAC
    (by dsimp only [PairAlg.W]; rw [← map_zero toRat]; exact regAt_toRat r 0)
    (by dsimp only [PairAlg.W]; rw [← map_one toRat]; exact regAt_toRat r 1)
private lemma regAC_U_C (r : L) : RegAC r U_C := by
  have : U_C = polyC X := by simp [U_C, polyC, RatFunc.algebraMap_X]
  rw [this]; exact regAC_polyC r X

private lemma regAC_add {r : L} {x y : A_C} (hx : RegAC r x) (hy : RegAC r y) : RegAC r (x + y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_add]
  exact regAC_evalAC (regAt_add hx.c0 hy.c0) (regAt_add hx.c1 hy.c1)

private lemma regAC_sub {r : L} {x y : A_C} (hx : RegAC r x) (hy : RegAC r y) : RegAC r (x - y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_sub]
  exact regAC_evalAC (regAt_sub hx.c0 hy.c0) (regAt_sub hx.c1 hy.c1)

private lemma regAC_neg {r : L} {x : A_C} (hx : RegAC r x) : RegAC r (-x) := by
  rw [← evalAC_coordsAC x, ← evalAC_neg]
  exact regAC_evalAC (regAt_neg hx.c0) (regAt_neg hx.c1)

private lemma regAC_mul {r : L} {x y : A_C} (hx : RegAC r x) (hy : RegAC r y) : RegAC r (x * y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_mul]
  exact regAC_evalAC
    (regAt_sub (regAt_mul hx.c0 hy.c0) (regAt_mul (regAt_mul hx.c1 hy.c1) (regAt_toRat r k5Params.cW)))
    (regAt_sub (regAt_add (regAt_mul hx.c0 hy.c1) (regAt_mul hx.c1 hy.c0))
      (regAt_mul (regAt_mul hx.c1 hy.c1) (regAt_toRat r k5Params.bW)))

private lemma regAC_pow {r : L} {x : A_C} (hx : RegAC r x) (n : ℕ) : RegAC r (x ^ n) := by
  induction n with
  | zero => simpa using regAC_one r
  | succ k ih => rw [pow_succ]; exact regAC_mul ih hx

private lemma regAC_div_rat {r : L} {x : A_C} {g : RatFunc K5}
    (hx : RegAC r x) (hg : RegUnitAt r g) : RegAC r (x / ιC_rat g) := by
  rw [div_eq_mul_inv, ← map_inv₀]
  exact regAC_mul hx (regAC_ιC_rat (regAt_inv hg))

private lemma regAC_div_polyC {r : L} {x : A_C} {P : K5[X]}
    (hx : RegAC r x) (hP : (P.map (algebraMap K5 L)).eval r ≠ 0) : RegAC r (x / polyC P) :=
  regAC_div_rat hx (regUnitAt_toRat hP)

private lemma regAC_div_ofNat {r : L} {x : A_C} (hx : RegAC r x) (n : ℕ) [n.AtLeastTwo]
    (hn : (OfNat.ofNat n : L) ≠ 0) : RegAC r (x / OfNat.ofNat n) := by
  have heq : (OfNat.ofNat n : A_C) = polyC (C (OfNat.ofNat n)) := by
    simp [polyC, map_ofNat]
  rw [heq]
  exact regAC_div_polyC hx (by rw [Polynomial.map_C, eval_C, map_ofNat]; exact hn)

private lemma nmAC_pairC (x : PairAlg K5[X]) : nmAC (pairC x) = toRat (k5Params.pnm x) := by
  simp only [nmAC, pairC, coordsAC_evalAC, CoverParams.pnm, PairAlg.nm, PairAlg.map,
    map_add, map_sub, map_mul, map_pow]

private lemma regAC_div_pairC {r : L} {x : A_C} {y : PairAlg K5[X]}
    (hx : RegAC r x) (hnm : ((k5Params.pnm y).map (algebraMap K5 L)).eval r ≠ 0) :
    RegAC r (x / pairC y) := by
  have hy_conj : pairC y * evalAC (PairAlg.conj (toRat k5Params.bW) (PairAlg.map toRat y)) =
      polyC (k5Params.pnm y) := by
    rw [pairC, ← evalAC_mul, polyC, ← evalAC_ofScalar]
    congr 1; ext
    · simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map, CoverParams.pnm,
        PairAlg.nm, map_add, map_sub, map_mul, map_pow]; ring
    · simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map]; ring
  have hnm_ne : k5Params.pnm y ≠ 0 := fun h0 => hnm (by rw [h0, Polynomial.map_zero, eval_zero])
  have hy_ne : pairC y ≠ 0 := pairC_ne_zero_of_pnm hnm_ne
  have hdiv : x / pairC y = (x * evalAC (PairAlg.conj (toRat k5Params.bW) (PairAlg.map toRat y))) /
      polyC (k5Params.pnm y) := by
    rw [div_eq_div_iff hy_ne (polyC_ne_zero hnm_ne)]
    linear_combination -x * hy_conj
  rw [hdiv]
  refine regAC_div_polyC (regAC_mul hx ?_) hnm
  exact regAC_evalAC
    (regAt_sub (regAt_toRat r y.c0) (regAt_mul (regAt_toRat r y.c1) (regAt_toRat r k5Params.bW)))
    (regAt_neg (regAt_toRat r y.c1))

private lemma regAC_div_W_C {r : L} {x : A_C} (hx : RegAC r x) (hr0 : r ≠ 0) :
    RegAC r (x / W_C) := by
  have hW : W_C = pairC PairAlg.W := by simp [pairC, PairAlg.map_W, evalAC_W]
  rw [hW]
  refine regAC_div_pairC hx ?_
  have hcW : k5Params.pnm PairAlg.W = k5Params.cW := by
    simp [CoverParams.pnm, PairAlg.nm, PairAlg.W]
  rw [hcW]; exact cW_eval_ne_zero hr0

private lemma regAC_div_U_C {r : L} {x : A_C} (hx : RegAC r x) (hr0 : r ≠ 0) :
    RegAC r (x / U_C) := by
  have hU : U_C = polyC X := by simp [U_C, polyC, RatFunc.algebraMap_X]
  rw [hU]; exact regAC_div_polyC hx (by simpa using hr0)

private lemma regAC_V_C {r : L} (hr0 : r ≠ 0) : RegAC r V_C :=
  regAC_div_U_C (regAC_W_C r) hr0

private lemma regAC_div_V_C {r : L} {x : A_C} (hx : RegAC r x) (hr0 : r ≠ 0) :
    RegAC r (x / V_C) := by
  rw [V_C, div_div_eq_mul_div]
  exact regAC_div_W_C (regAC_mul hx (regAC_U_C r)) hr0

private lemma regAC_div_u_of {r : L} {x : A_C} (hx : RegAC r x) (hr1 : r ≠ 1) :
    RegAC r (x / u_of U_C) := by
  have hu : u_of U_C = polyC (X - 1) / 9 := by
    simp [u_of, U_C, polyC, RatFunc.algebraMap_X]
  rw [hu, div_div_eq_mul_div]
  exact regAC_div_polyC (regAC_mul hx (regAC_ofNat r 9)) (by simpa [sub_eq_zero] using hr1)

private lemma regAC_div_v_of {r : L} {x : A_C} (hx : RegAC r x)
    (hnm : (k5Params.nm_WU.map (algebraMap K5 L)).eval r ≠ 0) :
    RegAC r (x / v_of V_C) := by
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hv : v_of V_C = pairC ⟨-X, 1⟩ / (9 * U_C) := by
    have heq : pairC ⟨-X, 1⟩ = W_C - U_C := by
      simp [pairC, evalAC, PairAlg.map, U_C, RatFunc.algebraMap_X]; ring
    rw [heq, v_of, V_C, eq_div_iff (mul_ne_zero h9 U_C_ne_zero)]
    have h1 : (9 : A_C) * ((W_C / U_C - 1) / 9) = W_C / U_C - 1 := mul_div_cancel₀ _ h9
    have h2 : U_C * (W_C / U_C - 1) = W_C - U_C := by
      rw [mul_sub, mul_div_cancel₀ _ U_C_ne_zero, mul_one]
    linear_combination U_C * h1 + h2
  rw [hv, div_div_eq_mul_div]
  exact regAC_div_pairC (regAC_mul hx (regAC_mul (regAC_ofNat r 9) (regAC_U_C r))) hnm

private lemma regAC_div_G_sq {r : L} {x : A_C} (hx : RegAC r x)
    (hG : ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval r ≠ 0) :
    RegAC r (x / G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C ^ 2) := by
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hGeq : G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C =
      pairC P_G_pair / (9 * U_C) := by
    rw [eq_div_iff (mul_ne_zero h9 U_C_ne_zero), mul_comm, nine_U_G_AC_eq]
  rw [hGeq, div_pow, div_div_eq_mul_div, pow_two (pairC P_G_pair), ← div_div]
  exact regAC_div_pairC (regAC_div_pairC
    (regAC_mul hx (regAC_pow (regAC_mul (regAC_ofNat r 9) (regAC_U_C r)) 2)) hG) hG

private lemma regAt_trace_euler_pairC {r : L} {x : A_C} {y : PairAlg K5[X]}
    (hx : RegAC r x) (hnm : ((k5Params.pnm y).map (algebraMap K5 L)).eval r ≠ 0) :
    RegAt r (Algebra.trace (RatFunc K5) A_C (x / (pairC y * (2 * W_C + polyC k5Params.bW)))) := by
  have hnm_ne : k5Params.pnm y ≠ 0 := fun h0 => hnm (by rw [h0, Polynomial.map_zero, eval_zero])
  have hnm_rat : PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) (PairAlg.map toRat y) ≠ 0 := by
    rw [← PairAlg.map_nm, show PairAlg.nm k5Params.bW k5Params.cW y = k5Params.pnm y from rfl]
    exact polynomialMap_ne_zero hnm_ne
  rw [← evalAC_coordsAC x, pairC, polyC, trace_AC_euler (coordsAC x) (PairAlg.map toRat y) hnm_rat]
  rw [← PairAlg.map_nm, show PairAlg.nm k5Params.bW k5Params.cW y = k5Params.pnm y from rfl]
  exact regAt_div
    (regAt_sub (regAt_mul hx.c1 (regAt_toRat r y.c0)) (regAt_mul hx.c0 (regAt_toRat r y.c1)))
    (regUnitAt_toRat hnm)

-- Polynomial `P18` components are always `RegAC r` whenever `a, b, U, V` are `RegAC r`!
private lemma regAC_poly_components {r : L} {a b : A_C} (ha : RegAC r a) (hb : RegAC r b) (hr0 : r ≠ 0) :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K
    let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let ξS := S - a * T; let ξQ := Q - b * T
    RegAC r (A_0U a b ξS ξQ U_C V_C / U_C + A_0V a b ξS ξQ U_C V_C / V_C) ∧
    RegAC r (A_Y a b ξS ξQ U_C V_C) ∧
    RegAC r (A_X a b ξS ξQ U_C V_C) ∧
    RegAC r (H0_of S Q T) ∧
    RegAC r (A1_of S Q U_C V_C) ∧
    RegAC r (B1_of T U_C V_C) ∧
    RegAC r (dot_ab (QY_num S Q T x y U_C V_C) a b) ∧
    RegAC r (dot_ab (QX_num S Q T x y U_C V_C) a b) ∧
    RegAC r (dot_ab (CY_of S Q T x y U_C V_C) a b) ∧
    RegAC r (dot_ab (CX_of S Q T x y U_C V_C) a b) ∧
    RegAC r (cA1_of S Q T a b U_C V_C) ∧
    RegAC r (cB1_of S Q T a b U_C V_C) ∧
    RegAC r (EB_of S Q T x y U_C V_C) := by
  intro S Q T x y ξS ξQ
  have hS : RegAC r S := regAC_ιC_K5 r S_K
  have hQ : RegAC r Q := regAC_ιC_K5 r Q_K
  have hT : RegAC r T := regAC_ιC_K5 r T_K
  have hx : RegAC r x := regAC_ιC_K5 r x_K
  have hy : RegAC r y := regAC_ιC_K5 r y_K
  have hU : RegAC r U_C := regAC_U_C r
  have hV : RegAC r V_C := regAC_V_C hr0
  have hξS : RegAC r ξS := regAC_sub hS (regAC_mul ha hT)
  have hξQ : RegAC r ξQ := regAC_sub hQ (regAC_mul hb hT)
  have hdiv_nat {z : A_C} (hz : RegAC r z) (n : ℕ) [hn2 : n.AtLeastTwo] : RegAC r (z / OfNat.ofNat n) := by
    have : CharZero L := charZero_of_injective_ringHom (algebraMap K5 L).injective
    have hn : (OfNat.ofNat n : L) ≠ 0 := by
      change (n : L) ≠ 0
      exact Nat.cast_ne_zero.mpr (by have := hn2.prop; omega)
    exact regAC_div_ofNat hz n hn
  have hclose_poly : ∀ (s q : A_C), RegAC r s → RegAC r q → RegAC r (dH_dS s q U_C V_C) := fun s q hs hq => by
    dsimp only [dH_dS]
    repeat (with_reducible (first | exact hs | exact hq | exact hU | exact hV |
                      exact regAC_ofNat r _ | apply hdiv_nat | apply regAC_add |
                      apply regAC_sub | apply regAC_neg | apply regAC_mul | apply regAC_pow))
  have hdHQ : ∀ (s q v0 : A_C), RegAC r s → RegAC r q → RegAC r v0 → RegAC r (dH_dQ s q v0 U_C V_C) :=
    fun s q v0 hs hq hv0 => by
      dsimp only [dH_dQ]
      repeat (with_reducible (first | exact hs | exact hq | exact hv0 | exact hU | exact hV |
                        exact regAC_ofNat r _ | apply hdiv_nat | apply regAC_add |
                        apply regAC_sub | apply regAC_neg | apply regAC_mul | apply regAC_pow))
  have hnumM (mi : Fin 10) : RegAC r (numM mi a b ξS ξQ U_C V_C) := by
    have ha2 : RegAC r (q1_a2 a b U_C V_C) := hclose_poly a b ha hb
    have ha0 : RegAC r (q1_a0 ξS ξQ U_C V_C) := hclose_poly ξS ξQ hξS hξQ
    have ha1 : RegAC r (q1_a1 a b ξS ξQ U_C V_C) :=
      regAC_sub (regAC_sub (hclose_poly _ _ (regAC_add ha hξS) (regAC_add hb hξQ)) ha2) ha0
    have hb2 : RegAC r (q2_b2 a b U_C V_C) := hdHQ a b 0 ha hb (regAC_zero r)
    have hb0 : RegAC r (q2_b0 ξS ξQ U_C V_C) := hdHQ ξS ξQ 1 hξS hξQ (regAC_one r)
    have hb1 : RegAC r (q2_b1 a b ξS ξQ U_C V_C) := by
      have h00 := hdHQ (a + ξS) (b + ξQ) 0 (regAC_add ha hξS) (regAC_add hb hξQ) (regAC_zero r)
      have h01 := hdHQ ξS ξQ 0 hξS hξQ (regAC_zero r)
      exact regAC_add (regAC_sub (regAC_sub h00 hb2) h01)
        (regAC_mul (regAC_mul (regAC_mul (hdiv_nat (regAC_ofNat r 10) 7) hb) hU) hV)
    have hd20 := regAC_sub (regAC_mul ha2 hb0) (regAC_mul ha0 hb2)
    have hd21 := regAC_sub (regAC_mul ha2 hb1) (regAC_mul ha1 hb2)
    have hd10 := regAC_sub (regAC_mul ha1 hb0) (regAC_mul ha0 hb1)
    have hcomb {m2 m1 m0 : A_C} (hm2 : RegAC r m2) (hm1 : RegAC r m1) (hm0 : RegAC r m0) :
        RegAC r ((1 / 16) * (m2 * (q1_a1 a b ξS ξQ U_C V_C * q2_b0 ξS ξQ U_C V_C -
            q1_a0 ξS ξQ U_C V_C * q2_b1 a b ξS ξQ U_C V_C) -
          m1 * (q1_a2 a b U_C V_C * q2_b0 ξS ξQ U_C V_C -
            q1_a0 ξS ξQ U_C V_C * q2_b2 a b U_C V_C) +
          m0 * (q1_a2 a b U_C V_C * q2_b1 a b ξS ξQ U_C V_C -
            q1_a1 a b ξS ξQ U_C V_C * q2_b2 a b U_C V_C))) :=
      regAC_mul (hdiv_nat (regAC_one r) 16)
        (regAC_add (regAC_sub (regAC_mul hm2 hd10) (regAC_mul hm1 hd20)) (regAC_mul hm0 hd21))
    fin_cases mi
    · exact hcomb (regAC_pow ha 2) (regAC_mul (regAC_mul (regAC_ofNat r 2) ha) hξS) (regAC_pow hξS 2)
    · exact hcomb (regAC_mul ha hb) (regAC_add (regAC_mul ha hξQ) (regAC_mul hb hξS)) (regAC_mul hξS hξQ)
    · exact hcomb (regAC_pow hb 2) (regAC_mul (regAC_mul (regAC_ofNat r 2) hb) hξQ) (regAC_pow hξQ 2)
    · exact hcomb ha hξS (regAC_zero r)
    · exact hcomb (regAC_zero r) ha hξS
    · exact hcomb hb hξQ (regAC_zero r)
    · exact hcomb (regAC_zero r) hb hξQ
    · exact hcomb (regAC_one r) (regAC_zero r) (regAC_zero r)
    · exact hcomb (regAC_zero r) (regAC_one r) (regAC_zero r)
    · exact hcomb (regAC_zero r) (regAC_zero r) (regAC_one r)
  have hA0U : RegAC r (A_0U a b ξS ξQ U_C V_C) := by
    dsimp only [A_0U]
    repeat (with_reducible (first | exact hnumM _ | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hA0V : RegAC r (A_0V a b ξS ξQ U_C V_C) := by
    dsimp only [A_0V]
    repeat (with_reducible (first | exact hnumM _ | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hAY : RegAC r (A_Y a b ξS ξQ U_C V_C) := by
    dsimp only [A_Y]
    repeat (with_reducible (first | exact hU | exact hV | exact hnumM _ | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hAX : RegAC r (A_X a b ξS ξQ U_C V_C) := by
    dsimp only [A_X]
    repeat (with_reducible (first | exact hU | exact hnumM _ | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hu : RegAC r (u_of U_C) := hdiv_nat (regAC_sub hU (regAC_one r)) 9
  have hv : RegAC r (v_of V_C) := hdiv_nat (regAC_sub hV (regAC_one r)) 9
  have hH0 : RegAC r (H0_of S Q T) := by
    dsimp only [H0_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hT | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg |
                    apply regAC_mul | apply regAC_pow))
  have hdH0 (k : Fin 3) : RegAC r (dH0_fn k S Q T) := by
    fin_cases k <;> dsimp only [dH0_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hT | exact regAC_ofNat r _ |
                      apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg |
                      apply regAC_mul | apply regAC_pow))
  have hdF5 (k : Fin 5) : RegAC r (dF5_fn k S Q T x y) := by
    fin_cases k <;> dsimp only [dF5_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hT | exact hx | exact hy | exact hdH0 _ | exact regAC_ofNat r _ |
                      apply regAC_add | apply regAC_mul | apply regAC_pow))
  have hu3 : RegAC r (u3_of S Q x) := by
    dsimp only [u3_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hx | exact regAC_ofNat r _ |
                    apply regAC_add | apply regAC_sub | apply regAC_mul))
  have hv3 : RegAC r (v3_of T y) := by
    dsimp only [v3_of]
    repeat (with_reducible (first | exact hT | exact hy | exact regAC_ofNat r _ |
                    apply regAC_add | apply regAC_sub))
  have hDX2 : RegAC r (DX2_of S Q x) := by
    dsimp only [DX2_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hu3 | exact regAC_ofNat r _ |
                    apply regAC_add | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  have hDY2 : RegAC r (DY2_of T y) := by
    dsimp only [DY2_of]
    repeat (with_reducible (first | exact hT | exact hv3 | exact regAC_ofNat r _ |
                    apply regAC_add | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  have hW2 : RegAC r (W2_of S Q T x y) := regAC_mul (regAC_mul (regAC_mul hS hT) hDX2) hDY2
  have hG : RegAC r (G_of S Q T x y U_C V_C) := regAC_add (regAC_mul hu hDX2) (regAC_mul hv hDY2)
  have hLX : RegAC r (LX_of S Q x U_C) := by
    dsimp only [LX_of]
    repeat (with_reducible (first | exact hu | exact hS | exact hQ | exact hu3 | exact hU |
                    exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_mul))
  have hLY : RegAC r (LY_of T y V_C) := by
    dsimp only [LY_of]
    repeat (with_reducible (first | exact hv | exact hT | exact hv3 | exact hV |
                    exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_mul))
  have hdLX (k : Fin 5) : RegAC r (dLX_fn k U_C) := by
    fin_cases k <;> dsimp only [dLX_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hu | exact hU | exact regAC_zero r | exact regAC_ofNat r _ |
                      apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hdLY (k : Fin 5) : RegAC r (dLY_fn k V_C) := by
    fin_cases k <;> dsimp only [dLY_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hv | exact hV | exact regAC_zero r | exact regAC_ofNat r _ |
                      apply hdiv_nat | apply regAC_add | apply regAC_neg | apply regAC_mul))
  have hbr (k : Fin 5) : RegAC r (br_fn k S Q T x y U_C V_C) := by
    dsimp only [br_fn]
    refine regAC_add ?_ (regAC_mul (regAC_mul (regAC_mul (regAC_ofNat r 2) hS) hT)
      (regAC_sub (regAC_mul hLX (hdLY k)) (regAC_mul hLY (hdLX k))))
    split
    · exact regAC_mul (regAC_mul (regAC_neg hT) hLX) hLY
    · exact regAC_mul (regAC_mul hS hLX) hLY
    · exact regAC_zero r
  have hd01 (m : Fin 5) : RegAC r (match m with | 0 => 1 | _ => 0) := by
    split
    · exact regAC_one r
    · exact regAC_zero r
  have hd21 (m : Fin 5) : RegAC r (match m with | 2 => 1 | _ => 0) := by
    split
    · exact regAC_one r
    · exact regAC_zero r
  have hdbr (k j : Fin 5) : RegAC r (dbr_fn k j S Q T x y U_C V_C) := by
    dsimp only [dbr_fn]
    refine regAC_add (regAC_add ?_
      (regAC_mul (regAC_mul (regAC_ofNat r 2) (regAC_add (regAC_mul (hd01 j) hT) (regAC_mul hS (hd21 j))))
        (regAC_sub (regAC_mul hLX (hdLY k)) (regAC_mul hLY (hdLX k)))))
      (regAC_mul (regAC_mul (regAC_mul (regAC_ofNat r 2) hS) hT)
        (regAC_sub (regAC_mul (hdLX j) (hdLY k)) (regAC_mul (hdLY j) (hdLX k))))
    split
    · exact regAC_neg (regAC_add (regAC_add (regAC_mul (regAC_mul (hd21 j) hLX) hLY)
        (regAC_mul (regAC_mul hT (hdLX j)) hLY)) (regAC_mul (regAC_mul hT hLX) (hdLY j)))
    · exact regAC_add (regAC_add (regAC_mul (regAC_mul (hd01 j) hLX) hLY)
        (regAC_mul (regAC_mul hS (hdLX j)) hLY)) (regAC_mul (regAC_mul hS hLX) (hdLY j))
    · exact regAC_zero r
  have hdDX2 (k : Fin 5) : RegAC r (dDX2_fn k S Q x) := by
    fin_cases k <;> dsimp only [dDX2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hu3 | exact regAC_zero r | exact regAC_ofNat r _ |
                      apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul | apply regAC_pow))
  have hdDY2 (k : Fin 5) : RegAC r (dDY2_fn k T y) := by
    fin_cases k <;> dsimp only [dDY2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hT | exact hv3 | exact regAC_zero r | exact regAC_one r | exact regAC_ofNat r _ |
                      apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul | apply regAC_pow))
  have hdW2 (k : Fin 5) : RegAC r (dW2_fn k S Q T x y) := by
    dsimp only [dW2_fn]
    exact regAC_add (regAC_add (regAC_add
      (regAC_mul (regAC_mul (regAC_mul (hd01 k) hT) hDX2) hDY2)
      (regAC_mul (regAC_mul (regAC_mul hS (hd21 k)) hDX2) hDY2))
      (regAC_mul (regAC_mul (regAC_mul hS hT) (hdDX2 k)) hDY2))
      (regAC_mul (regAC_mul (regAC_mul hS hT) hDX2) (hdDY2 k))
  have hdG (k : Fin 5) : RegAC r (dG_fn k S Q T x y U_C V_C) :=
    regAC_add (regAC_mul hu (hdDX2 k)) (regAC_mul hv (hdDY2 k))
  have hFc (f2 : Fin 5 → Fin 5 → A_C) (hf2 : ∀ i j, RegAC r (f2 i j)) (i : Fin 3) :
      RegAC r (F_contract S Q T x y f2 i) := by
    fin_cases i <;> dsimp only [F_contract, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      exact regAC_add (regAC_add (regAC_mul (hdF5 4) (hf2 _ 3)) (regAC_mul (hdF5 3) (hf2 4 _)))
        (regAC_mul (hdF5 _) (hf2 3 4))
  have hdot (v : Fin 3 → A_C) (hv_reg : ∀ i, RegAC r (v i)) : RegAC r (dot_ab v a b) :=
    regAC_add (regAC_add (regAC_mul (hv_reg 0) ha) (regAC_mul (hv_reg 1) hb)) (hv_reg 2)
  have hom (i j : Fin 5) : RegAC r (om_fn i j S Q T x y U_C V_C) := by
    dsimp only [om_fn]
    have homX (k : Fin 5) : RegAC r (match k with
        | 0 => -25 * S * U_C + 15 * Q * U_C + 9 * x * U_C + 25 * S - 15 * Q
        | 1 => 30 * (U_C - 1) * S
        | 3 => 18 * U_C * S
        | _ => 0) := by
      split <;>
        repeat (with_reducible (first | exact hS | exact hQ | exact hx | exact hU |
                        exact regAC_zero r | exact regAC_one r | exact regAC_ofNat r _ |
                        apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
    have homY (k : Fin 5) : RegAC r (match k with
        | 2 => -25 * T * V_C + 9 * y * V_C + 25 * T + 15 * V_C - 15
        | 4 => 18 * V_C * T
        | _ => 0) := by
      split <;>
        repeat (with_reducible (first | exact hT | exact hy | exact hV |
                        exact regAC_zero r | exact regAC_ofNat r _ |
                        apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
    exact regAC_mul (hdiv_nat (regAC_one r) 81)
      (regAC_sub (regAC_mul (homX i) (homY j)) (regAC_mul (homX j) (homY i)))
  have hcurl (Phi : Fin 5 → A_C) (dPhi : Fin 5 → Fin 5 → A_C)
      (hP : ∀ k, RegAC r (Phi k)) (hdP : ∀ k l, RegAC r (dPhi k l)) (i j : Fin 5) :
      RegAC r (curl_num_fn Phi dPhi S Q T x y U_C V_C i j) := by
    dsimp only [curl_num_fn]
    repeat (with_reducible (first | exact hW2 | exact hG | exact hP _ | exact hdP _ _ | exact hdW2 _ | exact hdG _ |
                    exact regAC_ofNat r _ | apply regAC_sub | apply regAC_mul))
  have hA1 : RegAC r (A1_of S Q U_C V_C) := by
    dsimp only [A1_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hU | exact hV | exact regAC_one r | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  have hB1 : RegAC r (B1_of T U_C V_C) := by
    dsimp only [B1_of]
    repeat (with_reducible (first | exact hT | exact hU | exact hV | exact regAC_one r | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  have hdA1 (k : Fin 3) : RegAC r (dA1_fn k S Q U_C V_C) := by
    fin_cases k <;> dsimp only [dA1_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hU | exact hV |
                      exact regAC_zero r | exact regAC_one r | exact regAC_ofNat r _ |
                      apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg |
                      apply regAC_mul | apply regAC_pow))
  have hdB1 : RegAC r (dB1_dT T U_C V_C) := by
    dsimp only [dB1_dT]
    repeat (with_reducible (first | exact hT | exact hU | exact hV | exact regAC_one r | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  refine ⟨regAC_add (regAC_div_U_C hA0U hr0) (regAC_div_V_C hA0V hr0), hAY, hAX, hH0, hA1, hB1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hdot _ (fun i => regAC_mul hDY2 (regAC_sub
      (regAC_mul hDX2 (hFc _ (fun p q => regAC_mul (regAC_mul hS hT) (hom p q)) i))
      (hFc _ (fun p q => regAC_mul (regAC_mul hS hT)
        (regAC_sub (regAC_mul (hdDX2 p) (hbr q)) (regAC_mul (hdDX2 q) (hbr p)))) i)))
  · exact hdot _ (fun i => regAC_mul hDX2 (regAC_add
      (regAC_mul (regAC_neg hDY2) (hFc _ (fun p q => regAC_mul (regAC_mul hS hT) (hom p q)) i))
      (hFc _ (fun p q => regAC_mul (regAC_mul hS hT)
        (regAC_sub (regAC_mul (hdDY2 p) (hbr q)) (regAC_mul (hdDY2 q) (hbr p)))) i)))
  · exact hdot _ (fun i => hFc _ (fun p q => hcurl _ _ (fun k => regAC_mul hDY2 (hbr k))
      (fun k l => regAC_add (regAC_mul (hdDY2 l) (hbr k)) (regAC_mul hDY2 (hdbr k l))) p q) i)
  · exact hdot _ (fun i => hFc _ (fun p q => hcurl _ _ (fun k => regAC_mul (regAC_neg hDX2) (hbr k))
      (fun k l => regAC_sub (regAC_mul (regAC_neg (hdDX2 l)) (hbr k)) (regAC_mul hDX2 (hdbr k l))) p q) i)
  · dsimp only [cA1_of]
    repeat (with_reducible (first | exact hH0 | exact hA1 | exact ha | exact hb | exact hdA1 _ | exact hdH0 _ |
                    apply regAC_add | apply regAC_sub | apply regAC_mul))
  · dsimp only [cB1_of]
    repeat (with_reducible (first | exact hH0 | exact hB1 | exact ha | exact hb | exact hdB1 | exact hdH0 _ |
                    apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  · dsimp only [EB_of]
    repeat (with_reducible (first | exact hW2 | exact hdF5 _ | exact hbr _ | exact regAC_ofNat r _ |
                    apply regAC_sub | apply regAC_mul))

private lemma regAC_interp4 {r : L} {f : A_C → A_C}
    (hf : ∀ z : A_C, RegAC r z → RegAC r (f z)) :
    let p := interp4 f
    RegAC r p.1 ∧ RegAC r p.2.1 ∧ RegAC r p.2.2.1 ∧ RegAC r p.2.2.2.1 ∧ RegAC r p.2.2.2.2 := by
  have hdiv_nat {z : A_C} (hz : RegAC r z) (n : ℕ) [hn2 : n.AtLeastTwo] : RegAC r (z / OfNat.ofNat n) := by
    have : CharZero L := charZero_of_injective_ringHom (algebraMap K5 L).injective
    have hn : (OfNat.ofNat n : L) ≠ 0 := by
      change (n : L) ≠ 0
      exact Nat.cast_ne_zero.mpr (by have := hn2.prop; omega)
    exact regAC_div_ofNat hz n hn
  have h0 := hf 0 (regAC_zero r)
  have h1 := hf 1 (regAC_one r)
  have hm1 := hf (-1) (regAC_neg (regAC_one r))
  have h2 := hf 2 (regAC_ofNat r 2)
  have hm2 := hf (-2) (regAC_neg (regAC_ofNat r 2))
  simp only [interp4]
  refine ⟨?_, ?_, ?_, ?_, h0⟩
  · exact hdiv_nat (regAC_add (regAC_add (regAC_mul (regAC_neg (regAC_ofNat r 4)) (regAC_add h1 hm1))
      (regAC_add h2 hm2)) (regAC_mul (regAC_ofNat r 6) h0)) 24
  · exact hdiv_nat (regAC_add (regAC_mul (regAC_neg (regAC_ofNat r 2)) (regAC_sub h1 hm1))
      (regAC_sub h2 hm2)) 12
  · exact hdiv_nat (regAC_sub (regAC_sub (regAC_mul (regAC_ofNat r 16) (regAC_add h1 hm1))
      (regAC_add h2 hm2)) (regAC_mul (regAC_ofNat r 30) h0)) 24
  · exact hdiv_nat (regAC_sub (regAC_mul (regAC_ofNat r 8) (regAC_sub h1 hm1))
      (regAC_sub h2 hm2)) 12

private lemma regAC_remDeg4 {r : L} {q2 q1 q0 p4 p3 p2 p1 p0 : A_C}
    (hq2 : RegAC r q2) (hq1 : RegAC r q1) (hq0 : RegAC r q0)
    (hp4 : RegAC r p4) (hp3 : RegAC r p3) (hp2 : RegAC r p2)
    (hp1 : RegAC r p1) (hp0 : RegAC r p0) :
    RegAC r (remDeg4_P1 q2 q1 q0 p4 p3 p2 p1) ∧ RegAC r (remDeg4_P0 q2 q1 q0 p4 p3 p2 p0) := by
  have hr3 := regAC_sub (regAC_mul hq2 hp3) (regAC_mul hq1 hp4)
  have hr2 := regAC_sub (regAC_mul hq2 hp2) (regAC_mul hq0 hp4)
  have hs2 := regAC_sub (regAC_mul hq2 hr2) (regAC_mul hq1 hr3)
  have hs1 := regAC_sub (regAC_mul (regAC_pow hq2 2) hp1) (regAC_mul hq0 hr3)
  exact ⟨regAC_sub (regAC_mul hq2 hs1) (regAC_mul hq1 hs2),
         regAC_sub (regAC_mul (regAC_pow hq2 3) hp0) (regAC_mul hq0 hs2)⟩

private lemma regAC_remDeg3 {r : L} {q2 q1 q0 e3 e2 e1 e0 : A_C}
    (hq2 : RegAC r q2) (hq1 : RegAC r q1) (hq0 : RegAC r q0)
    (he3 : RegAC r e3) (he2 : RegAC r e2) (he1 : RegAC r e1) (he0 : RegAC r e0) :
    RegAC r (remDeg3_d1 q2 q1 q0 e3 e2 e1) ∧ RegAC r (remDeg3_d0 q2 q1 q0 e3 e2 e0) := by
  have ht2 := regAC_sub (regAC_mul hq2 he2) (regAC_mul hq1 he3)
  have ht1 := regAC_sub (regAC_mul hq2 he1) (regAC_mul hq0 he3)
  have ht0 := regAC_mul hq2 he0
  exact ⟨regAC_sub (regAC_mul hq2 ht1) (regAC_mul hq1 ht2),
         regAC_sub (regAC_mul hq2 ht0) (regAC_mul hq0 ht2)⟩

private lemma polyC_81_Av0_Q5_eq :
    polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3) =
      81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q5_z ^ 3 := by
  simp only [polyC, ιC_K5, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, RingHom.comp_apply]
  rfl

private lemma regAt_eta_of_P18_z {r : L} (hr0 : r ≠ 0)
    (hQ5 : (k5Params.Q5_z.map (algebraMap K5 L)).eval r ≠ 0)
    (hP34 : (P34_K5.map (algebraMap K5 L)).eval r ≠ 0)
    (hcb : (k5Params.cb_h.map (algebraMap K5 L)).eval r ≠ 0)
    (hP18 : ∀ z : A_C, RegAC r z → RegAC r (P18_z_AC z)) :
    RegAt r eta := by
  have h81K : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  have hnm_z : (k5Params.nm_z.map (algebraMap K5 L)).eval r ≠ 0 := by
    rw [nm_z_K5_factor]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_mul, eval_pow, eval_C, eval_X]
    have hcbm : (cb_h_m_K5.map (algebraMap K5 L)).eval r ≠ 0 := by
      have h := congrArg (fun f : K5[X] => (f.map (algebraMap K5 L)).eval r) cb_h_K5_eq_mul_monic
      simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C] at h
      exact right_ne_zero_of_mul (h ▸ hcb)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr lc34_K5_ne_zero)
      (pow_ne_zero 15 hr0)) (pow_ne_zero 12 hcbm)) hP34
  have hnum_raw : RegAC r eta_AC_num := by
    obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ := regAC_interp4 hP18
    obtain ⟨hP1, hP0⟩ := regAC_remDeg4 (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _)
      hp4 hp3 hp2 hp1 hp0
    exact regAC_mul (regAC_mul (regAC_mul (regAC_neg (regAC_sub
      (regAC_mul hP1 (regAC_pairC r _)) (regAC_mul hP0 (regAC_pairC r _))))
      (regAC_pow (regAC_U_C r) 3)) (regAC_W_C r)) (regAC_pow (regAC_polyC r _) 4)
  have hnum : RegAC r (eta_AC_num / polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3)) := by
    refine regAC_div_polyC hnum_raw ?_
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, eval_mul, eval_pow, eval_C]
    exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr
      (mul_ne_zero h81K Av0_K5_ne_zero)) (pow_ne_zero 3 hQ5)
  have heta_eq : eta_AC = (eta_AC_num / polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3)) /
      (pairC k5Params.res_z * (2 * W_C + polyC k5Params.bW)) := by
    rw [eta_AC, polyC_81_Av0_Q5_eq, div_div]
    exact congrArg (eta_AC_num / ·) (by ring)
  rw [eta, heta_eq]
  exact regAt_trace_euler_pairC hnum hnm_z

-- Proof that `δ 3` kills every coefficient of `k5Params.bW` and `k5Params.nm_WU` (purely in S, Q, T).
private lemma δ3_k5Params_consts :
    δ 3 k5Params.Av0_inv = 0 ∧ δ 3 k5Params.Cv0 = 0 ∧
    δ 3 k5Params.Bv0 = 0 ∧ δ 3 k5Params.Bv1 = 0 ∧ δ 3 k5Params.Bv2 = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  have hS : δ 3 S_K = 0 := by simp [δ_S]
  have hQ : δ 3 Q_K = 0 := by simp [δ_Q]
  have hT : δ 3 T_K = 0 := by simp [δ_T]
  have hinv (c : K5) (hc : δ 3 c = 0) : δ 3 c⁻¹ = 0 := by
    by_cases h : c = 0
    · subst h; simp
    · rw [(δ 3).leibniz_inv, hc, smul_zero]
  have hinv2 : δ 3 (2 : K5)⁻¹ = 0 := hinv 2 (δ_ofNat 3 2)
  have hinv3 : δ 3 (3 : K5)⁻¹ = 0 := hinv 3 (δ_ofNat 3 3)
  have hinv7 : δ 3 (7 : K5)⁻¹ = 0 := hinv 7 (δ_ofNat 3 7)
  have hinvT3 : δ 3 (T_K - 3)⁻¹ = 0 := hinv (T_K - 3) (by rw [map_sub, hT, δ_ofNat, sub_self])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [CoverParams.Av0_inv, CoverParams.Cv0, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2,
      CoverParams.inv4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
      k5Params_inv2, k5Params_inv3, k5Params_inv7, k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T,
      map_add, map_sub, map_neg, (δ 3).leibniz, (δ 3).leibniz_pow,
      hS, hQ, hT, hinv2, hinv3, hinv7, hinvT3, δ_ofNat,
      smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]

private lemma δ3_coeff_bW (k : ℕ) : δ 3 (k5Params.bW.coeff k) = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  obtain ⟨hAi, _, hB0, hB1, hB2⟩ := δ3_k5Params_consts
  rw [CoverParams.bW, CoverParams.Bv, CoverParams.quadU]
  rcases k with _ | _ | _ | k <;>
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      (δ 3).leibniz, hAi, hB0, hB1, hB2]

private lemma δ3_coeff_cW (k : ℕ) : δ 3 (k5Params.cW.coeff k) = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  obtain ⟨hAi, hC0, _, _, _⟩ := δ3_k5Params_consts
  rw [CoverParams.cW, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs
  · simp [(δ 3).leibniz, hAi, hC0]
  · simp

private lemma δ3_coeff_nm_WU (k : ℕ) : δ 3 (k5Params.nm_WU.coeff k) = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  have hmul (P Q : K5[X]) (hP : ∀ j, δ 3 (P.coeff j) = 0) (hQ : ∀ j, δ 3 (Q.coeff j) = 0) (m : ℕ) :
      δ 3 ((P * Q).coeff m) = 0 := by
    rw [Polynomial.coeff_mul, map_sum]
    apply Finset.sum_eq_zero; intro x _
    rw [(δ 3).leibniz, hP, hQ, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, add_zero]
  have hX (j : ℕ) : δ 3 ((X : K5[X]).coeff j) = 0 := by
    rw [Polynomial.coeff_X]; split_ifs <;> simp [(δ 3).map_one_eq_zero]
  have hnm : k5Params.nm_WU = X * X + X * k5Params.bW + k5Params.cW := by
    simp only [CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm]; ring
  rw [hnm, Polynomial.coeff_add, Polynomial.coeff_add, map_add, map_add,
    hmul _ _ hX hX, hmul _ _ hX δ3_coeff_bW, δ3_coeff_cW, add_zero, add_zero]

/-- At any root `r` of `nm_WU` in a finite extension `L / K5`, `nm(G)(r) ≠ 0` by `W_G_ne_zero`. -/
private lemma pnm_P_G_eval_ne_zero_of_nm_WU [FiniteDimensional K5 L] {r : L}
    (hr0 : r ≠ 0) (hnm : (k5Params.nm_WU.map (algebraMap K5 L)).eval r = 0) :
    ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval r ≠ 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  let _ : Algebra ℤ L := Ring.toIntAlgebra L
  have hr1 : r ≠ 1 := fun h1 => nm_WU_eval_one_ne (L := L) (h1 ▸ hnm)
  have hnm_exp : r ^ 2 + r * (k5Params.bW.map (algebraMap K5 L)).eval r +
      (k5Params.cW.map (algebraMap K5 L)).eval r = 0 := by
    have h := hnm
    simp only [CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_X,
      Polynomial.map_one, eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_X, eval_one] at h
    linear_combination h
  have hfac : ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval r =
      (algebraMap K5 L DX2_K * r * (r - 1)) *
      (r * (r - 1) * algebraMap K5 L DX2_K -
        (2 * r + (k5Params.bW.map (algebraMap K5 L)).eval r) * algebraMap K5 L DY2_K) := by
    simp only [CoverParams.pnm, P_G_pair, PairAlg.nm, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.map_one,
      eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_one]
    linear_combination (algebraMap K5 L DY2_K) ^ 2 * hnm_exp
  rw [hfac]
  have hc1_ne : r * (r - 1) ≠ 0 := mul_ne_zero hr0 (sub_ne_zero.mpr hr1)
  have hDX_ne : algebraMap K5 L DX2_K ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K5 L).injective).mpr DX2_K_ne_zero
  refine mul_ne_zero (by rw [mul_assoc]; exact mul_ne_zero hDX_ne hc1_ne) ?_
  -- Apply `δL 3` to `c1 * DX2 - c2 * DY2 = 0` and contradict `SheetCalculus.W_G_ne_zero`!
  intro hlin
  set c1 : L := r * (r - 1)
  set c2 : L := 2 * r + (k5Params.bW.map (algebraMap K5 L)).eval r
  have hδr : δL (L := L) 3 r = 0 :=
    δL3_eq_zero_of_isRoot k5Params.nm_WU nm_WU_K5_ne_zero δ3_coeff_nm_WU r hnm
  have hδbW : δL (L := L) 3 ((k5Params.bW.map (algebraMap K5 L)).eval r) = 0 := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le), map_sum]
    apply Finset.sum_eq_zero; intro k _
    rw [Polynomial.coeff_map, (δL (L := L) 3).leibniz, δL_apply, δ3_coeff_bW k, map_zero,
      (δL (L := L) 3).leibniz_pow, hδr]
    simp
  have hδc1 : δL (L := L) 3 c1 = 0 := by
    dsimp only [c1]
    rw [(δL (L := L) 3).leibniz, map_sub, hδr, (δL (L := L) 3).map_one_eq_zero]; simp
  have hδc2 : δL (L := L) 3 c2 = 0 := by
    dsimp only [c2]
    have h2 : δL (L := L) 3 (2 : L) = 0 := by
      change δL (L := L) 3 ((2 : ℕ) : L) = 0; exact (δL (L := L) 3).map_natCast 2
    rw [map_add, (δL (L := L) 3).leibniz, h2, hδr, hδbW]; simp
  have hd1 : δL (L := L) 3 (c1 * algebraMap K5 L DX2_K) = c1 * algebraMap K5 L (δ 3 DX2_K) := by
    rw [(δL (L := L) 3).leibniz, hδc1, δL_apply]; simp [smul_eq_mul]
  have hd2 : δL (L := L) 3 (c2 * algebraMap K5 L DY2_K) = c2 * algebraMap K5 L (δ 3 DY2_K) := by
    rw [(δL (L := L) 3).leibniz, hδc2, δL_apply]; simp [smul_eq_mul]
  have hd := congrArg (δL (L := L) 3) hlin
  rw [map_zero, map_sub, hd1, hd2] at hd
  have hWG : c1 * algebraMap K5 L (DX2_K * δ 3 DY2_K - DY2_K * δ 3 DX2_K) = 0 := by
    simp only [map_sub, map_mul]
    linear_combination algebraMap K5 L (δ 3 DY2_K) * hlin - algebraMap K5 L DY2_K * hd
  exact mul_ne_zero hc1_ne ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr W_G_ne_zero) hWG

/-- **Global Regularity Theorem**: For any finite extension `L / K5`, `eta_L` is regular at
every `r : L` outside `{0} ∪ R_{Q5} ∪ R_{34}`. -/
theorem regularAt_eta_of_ne [FiniteDimensional K5 L] (r : L)
    (hr0 : r ≠ 0)
    (hQ5 : (k5Params.Q5_z.map (algebraMap K5 L)).eval r ≠ 0)
    (hP34 : (P34_K5.map (algebraMap K5 L)).eval r ≠ 0) :
    RegularAt r (mapRatFunc (algebraMap K5 L) eta) := by
  have h81K : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  by_cases hcb : (k5Params.cb_h.map (algebraMap K5 L)).eval r = 0
  · -- Case 4: `cb_h(r) = 0` — use mirror `a`-elimination (`eta_AC_eq_a_elim`)!
    have hca : (k5Params.ca_h.map (algebraMap K5 L)).eval r ≠ 0 :=
      eval_ne_zero_of_isCoprime isCoprime_cb_h_ca_h hcb
    have hr1 : r ≠ 1 := by
      have h := eval_ne_zero_of_isCoprime isCoprime_cb_h_X_sub_1 hcb
      simpa [sub_eq_zero] using h
    have hnmWU : (k5Params.nm_WU.map (algebraMap K5 L)).eval r ≠ 0 :=
      eval_ne_zero_of_isCoprime isCoprime_cb_h_nm_WU hcb
    -- `nm_w(r) ≠ 0` from cancelling `cb_h_m^12` in `ca_h^12 * nm_z = cb_h^12 * nm_w`!
    have hnm_w : (k5Params.nm_w.map (algebraMap K5 L)).eval r ≠ 0 := by
      have hfac : C (((locParams.cb_h.coeff 2 : LocK5) : K5) ^ 12) * k5Params.nm_w =
          k5Params.ca_h ^ 12 * (C lc34_K5 * X ^ 15 * P34_K5) := by
        have h := k5Params_nm_z_elim_symm
        rw [nm_z_K5_factor, cb_h_K5_eq_mul_monic, mul_pow, ← map_pow] at h
        have hcbm12 : cb_h_m_K5 ^ 12 ≠ 0 :=
          pow_ne_zero 12 (cb_h_m_loc_spec.1.map LocK5.subtype).ne_zero
        apply mul_left_cancel₀ hcbm12
        linear_combination -h
      have hev := congrArg (fun f : K5[X] => (f.map (algebraMap K5 L)).eval r) hfac
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
        eval_mul, eval_pow, eval_C, eval_X] at hev
      have hrhs : ((k5Params.ca_h.map (algebraMap K5 L)).eval r) ^ 12 *
          (algebraMap K5 L lc34_K5 * r ^ 15 * (P34_K5.map (algebraMap K5 L)).eval r) ≠ 0 :=
        mul_ne_zero (pow_ne_zero 12 hca)
          (mul_ne_zero (mul_ne_zero
            ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr lc34_K5_ne_zero)
            (pow_ne_zero 15 hr0)) hP34)
      exact right_ne_zero_of_mul (hev.symm ▸ hrhs)
    have hP18w (w : A_C) (hw : RegAC r w) : RegAC r (P18_w_AC w) := by
      have ha : RegAC r (-(polyC k5Params.cb_h * w + pairC k5Params.c0W) / (W_C * polyC k5Params.ca_h)) := by
        rw [← div_div]
        exact regAC_div_polyC (regAC_div_W_C (regAC_neg (regAC_add
          (regAC_mul (regAC_polyC r _) hw) (regAC_pairC r _))) hr0) hca
      have hb : RegAC r (w / W_C) := regAC_div_W_C hw hr0
      obtain ⟨hM0, hMY, hMX, hH0, hA1, hB1, hQY, hQX, _, _, hcA1, _, hEB⟩ :=
        regAC_poly_components ha hb hr0
      unfold P18_w_AC P18_of
      have hqY := regAC_div_v_of hQY hnmWU
      have hqX := regAC_div_u_of hQX hr1
      exact regAC_add (regAC_mul hM0 (regAC_add (regAC_add
        (regAC_mul (regAC_mul hH0 hA1) hqY) (regAC_mul (regAC_mul hH0 hB1) hqX))
        (regAC_mul (regAC_div_v_of hcA1 hnmWU) hEB)))
        (regAC_mul (regAC_add (regAC_mul hMY hqY) (regAC_mul hMX hqX)) (regAC_pow hH0 2))
    have hnum_w_raw : RegAC r eta_AC_num_w := by
      obtain ⟨hq4, hq3, hq2, hq1, hq0⟩ := regAC_interp4 hP18w
      obtain ⟨hP1w, hP0w⟩ := regAC_remDeg4 (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _)
        hq4 hq3 hq2 hq1 hq0
      obtain ⟨hd1w, hd0w⟩ := regAC_remDeg3 (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _)
        (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _)
      exact regAC_mul (regAC_mul (regAC_mul
        (regAC_sub (regAC_mul hP1w hd0w) (regAC_mul hP0w hd1w))
        (regAC_pow (regAC_U_C r) 3)) (regAC_W_C r)) (regAC_pow (regAC_polyC r _) 4)
    have hnum_w : RegAC r (eta_AC_num_w / polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3)) := by
      refine regAC_div_polyC hnum_w_raw ?_
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, eval_mul, eval_pow, eval_C]
      exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr
        (mul_ne_zero h81K Av0_K5_ne_zero)) (pow_ne_zero 3 hQ5)
    have heta_w : eta_AC = (eta_AC_num_w / polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3)) /
        (pairC k5Params.res_w * (2 * W_C + polyC k5Params.bW)) := by
      rw [eta_AC_eq_a_elim, polyC_81_Av0_Q5_eq, div_div]
      exact congrArg (eta_AC_num_w / ·) (by ring)
    rw [eta, heta_w]
    exact regAt_trace_euler_pairC hnum_w hnm_w
  · -- Now `cb_h(r) ≠ 0`, so `a(z)` and `b(z)` are `RegAC r` for every `RegAC r z`!
    apply regAt_eta_of_P18_z hr0 hQ5 hP34 hcb
    intro z hz
    have ha : RegAC r (z / W_C) := regAC_div_W_C hz hr0
    have hb : RegAC r (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)) := by
      rw [← div_div]
      exact regAC_div_polyC (regAC_div_W_C (regAC_neg (regAC_add
        (regAC_mul (regAC_polyC r _) hz) (regAC_pairC r _))) hr0) hcb
    obtain ⟨hM0, hMY, hMX, hH0, hA1, hB1, hQY, hQX, hCY, hCX, hcA1, hcB1, hEB⟩ :=
      regAC_poly_components ha hb hr0
    by_cases hr1 : r = 1
    · -- Case 2: `r = 1` — use `P18_z_AC_eq_regX`!
      rw [P18_z_AC_eq_regX]
      have hnmWU : (k5Params.nm_WU.map (algebraMap K5 L)).eval r ≠ 0 := hr1 ▸ nm_WU_eval_one_ne
      have hG1 : ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval r ≠ 0 := by
        rw [hr1, pnm_P_G_eval_one]
        exact mul_ne_zero (pow_ne_zero 2 ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr DY2_K_ne_zero))
          nm_WU_eval_one_ne
      unfold P18_regX_of
      have hqY := regAC_div_v_of hQY hnmWU
      have hqX := regAC_div_G_sq hCX hG1
      exact regAC_add (regAC_mul hM0 (regAC_add (regAC_add
        (regAC_mul (regAC_mul hH0 hA1) hqY) (regAC_mul (regAC_mul hH0 hB1) hqX))
        (regAC_mul (regAC_div_v_of hcA1 hnmWU) hEB)))
        (regAC_mul (regAC_add (regAC_mul hMY hqY) (regAC_mul hMX hqX)) (regAC_pow hH0 2))
    · by_cases hnmWU : (k5Params.nm_WU.map (algebraMap K5 L)).eval r = 0
      · -- Case 3: `nm_WU(r) = 0` — use `P18_z_AC_eq_regY` + `W_G_ne_zero`!
        rw [P18_z_AC_eq_regY]
        have hGnm := pnm_P_G_eval_ne_zero_of_nm_WU hr0 hnmWU
        unfold P18_regY_of
        have hqY := regAC_div_G_sq hCY hGnm
        have hqX := regAC_div_u_of hQX hr1
        exact regAC_add (regAC_mul hM0 (regAC_add (regAC_add
          (regAC_mul (regAC_mul hH0 hA1) hqY) (regAC_mul (regAC_mul hH0 hB1) hqX))
          (regAC_mul (regAC_div_u_of (regAC_neg hcB1) hr1) hEB)))
          (regAC_mul (regAC_add (regAC_mul hMY hqY) (regAC_mul hMX hqX)) (regAC_pow hH0 2))
      · -- Case 1: Generic point!
        unfold P18_z_AC P18_of
        have hqY := regAC_div_v_of hQY hnmWU
        have hqX := regAC_div_u_of hQX hr1
        exact regAC_add (regAC_mul hM0 (regAC_add (regAC_add
          (regAC_mul (regAC_mul hH0 hA1) hqY) (regAC_mul (regAC_mul hH0 hB1) hqX))
          (regAC_mul (regAC_div_v_of hcA1 hnmWU) hEB)))
          (regAC_mul (regAC_add (regAC_mul hMY hqY) (regAC_mul hMX hqX)) (regAC_pow hH0 2))

end RegACProof

lemma regularAt_eta_L_of_notMem (r : CoverL)
    (hr : r ∉ ({0} ∪ RQ5 ∪ R34 : Finset CoverL)) :
    RegularAt r eta_L := by
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hr
  exact regularAt_eta_of_ne r hr.1.1 (fun h => hr.1.2 (mem_RQ5_iff.mpr h))
    (fun h => hr.2 (mem_R34_iff.mpr h))


end SymmetricSexticResidual.CoverResidue

open scoped Classical in
theorem solution
    (r : SymmetricSexticResidual.CoverResidue.CoverL)
    (hr : r ∉ ({0} ∪ SymmetricSexticResidual.CoverResidue.RQ5 ∪
      SymmetricSexticResidual.CoverResidue.R34 : Finset SymmetricSexticResidual.CoverResidue.CoverL)) :
    CrossedRationalResidue.RegularAt r SymmetricSexticResidual.CoverResidue.eta_L :=
  SymmetricSexticResidual.CoverResidue.regularAt_eta_L_of_notMem r hr
