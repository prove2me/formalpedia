-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_valAC_P18
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T09:36:22.824521+00:00
-- url     : https://prove2.me/submissions/323c5b35-e6cd-407b-bac1-6a30814cbce8

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

section RegACHelpers
variable {L : Type*} [Field L] [Algebra K5 L]
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
end RegACHelpers

section BranchEvalProof
private lemma valAC_evalAC (r w : CoverL) (p : PairAlg (RatFunc K5)) :
    valAC r w (evalAC p) = valueAt r (mapRatFunc ιL_K5 p.c0) + valueAt r (mapRatFunc ιL_K5 p.c1) * w := by
  simp only [valAC, coordsAC_evalAC]

private lemma valAC_zero (r w : CoverL) : ValAC r w 0 0 := by
  refine ⟨regAC_zero r, ?_⟩
  rw [← evalAC_zero, valAC_evalAC]; simp [PairAlg.zero]

private lemma valAC_one (r w : CoverL) : ValAC r w 1 1 := by
  refine ⟨regAC_one r, ?_⟩
  rw [← evalAC_one, valAC_evalAC, PairAlg.one]
  simp only [map_one, map_zero, zero_mul, add_zero]
  rw [show (1 : RatFunc CoverL) = RatFunc.C 1 from (map_one RatFunc.C).symm, valueAt_C]

private lemma valAC_ofNat (r w : CoverL) (n : ℕ) [n.AtLeastTwo] :
    ValAC r w (OfNat.ofNat n) (OfNat.ofNat n) := by
  refine ⟨regAC_ofNat r n, ?_⟩
  have h1 : (OfNat.ofNat n : A_C) = evalAC (PairAlg.ofScalar (OfNat.ofNat n)) := by
    rw [evalAC_ofScalar, map_ofNat]
  rw [h1, valAC_evalAC, PairAlg.ofScalar]
  simp only [map_ofNat, map_zero, zero_mul, add_zero]
  have hc : (OfNat.ofNat n : RatFunc CoverL) = RatFunc.C (OfNat.ofNat n) := (map_ofNat RatFunc.C n).symm
  rw [hc, valueAt_C]

private lemma valAC_ιC_K5 (r w : CoverL) (c : K5) : ValAC r w (ιC_K5 c) (ιL_K5 c) := by
  refine ⟨regAC_ιC_K5 r c, ?_⟩
  have h1 : ιC_K5 c = evalAC (PairAlg.ofScalar (RatFunc.C c)) := by
    rw [evalAC_ofScalar]; rfl
  rw [h1, valAC_evalAC, PairAlg.ofScalar]
  simp only [mapRatFunc_C, map_zero, valueAt_C, zero_mul, add_zero]

private lemma valAC_polyC (r w : CoverL) (P : K5[X]) :
    ValAC r w (polyC P) ((P.map ιL_K5).eval r) := by
  refine ⟨regAC_polyC r P, ?_⟩
  rw [polyC, ← evalAC_ofScalar, valAC_evalAC, PairAlg.ofScalar]
  simp only [mapRatFunc_algebraMap, map_zero, valueAt_polynomial, zero_mul, add_zero]

private lemma valAC_pairC (r w : CoverL) (y : PairAlg K5[X]) :
    ValAC r w (pairC y) (pUW ιL_K5 y r w) := by
  refine ⟨regAC_pairC r y, ?_⟩
  rw [pairC, valAC_evalAC, PairAlg.map]
  simp only [mapRatFunc_algebraMap, valueAt_polynomial]
  rfl

private lemma valAC_U_C (r w : CoverL) : ValAC r w U_C r := by
  refine ⟨regAC_U_C r, ?_⟩
  have hU : U_C = polyC X := by simp [U_C, polyC, RatFunc.algebraMap_X]
  rw [hU]; simpa using (valAC_polyC r w X).eq

private lemma valAC_W_C (r w : CoverL) : ValAC r w W_C w := by
  refine ⟨regAC_W_C r, ?_⟩
  rw [← evalAC_W, valAC_evalAC, PairAlg.W]
  simp only [map_zero, map_one, zero_add]
  rw [show (1 : RatFunc CoverL) = RatFunc.C 1 from (map_one RatFunc.C).symm, valueAt_C, one_mul]

private lemma valAC_add {r w : CoverL} {x y : A_C} {vx vy : CoverL}
    (hx : ValAC r w x vx) (hy : ValAC r w y vy) : ValAC r w (x + y) (vx + vy) := by
  refine ⟨regAC_add hx.reg hy.reg, ?_⟩
  have hxy : coordsAC (x + y) = PairAlg.add (coordsAC x) (coordsAC y) := by
    apply evalAC_injective; rw [evalAC_coordsAC, evalAC_add, evalAC_coordsAC, evalAC_coordsAC]
  rw [valAC, hxy, PairAlg.add]
  simp only [map_add]
  have h1 := hx.eq; have h2 := hy.eq; dsimp only [valAC] at h1 h2
  linear_combination h1 + h2

private lemma valAC_sub {r w : CoverL} {x y : A_C} {vx vy : CoverL}
    (hx : ValAC r w x vx) (hy : ValAC r w y vy) : ValAC r w (x - y) (vx - vy) := by
  refine ⟨regAC_sub hx.reg hy.reg, ?_⟩
  have hxy : coordsAC (x - y) = PairAlg.sub (coordsAC x) (coordsAC y) := by
    apply evalAC_injective; rw [evalAC_coordsAC, evalAC_sub, evalAC_coordsAC, evalAC_coordsAC]
  rw [valAC, hxy, PairAlg.sub]
  simp only [map_sub]
  have h1 := hx.eq; have h2 := hy.eq; dsimp only [valAC] at h1 h2
  linear_combination h1 - h2

private lemma valAC_neg {r w : CoverL} {x : A_C} {vx : CoverL}
    (hx : ValAC r w x vx) : ValAC r w (-x) (-vx) := by
  refine ⟨regAC_neg hx.reg, ?_⟩
  have hxy : coordsAC (-x) = PairAlg.neg (coordsAC x) := by
    apply evalAC_injective; rw [evalAC_coordsAC, evalAC_neg, evalAC_coordsAC]
  rw [valAC, hxy, PairAlg.neg]
  simp only [map_neg]
  have h1 := hx.eq; dsimp only [valAC] at h1
  linear_combination -h1

private lemma valAC_mul {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {x y : A_C} {vx vy : CoverL}
    (hx : ValAC r w x vx) (hy : ValAC r w y vy) : ValAC r w (x * y) (vx * vy) := by
  refine ⟨regAC_mul hx.reg hy.reg, ?_⟩
  have hxy : coordsAC (x * y) = PairAlg.mul (toRat k5Params.bW) (toRat k5Params.cW) (coordsAC x) (coordsAC y) := by
    apply evalAC_injective; rw [evalAC_coordsAC, evalAC_mul, evalAC_coordsAC, evalAC_coordsAC]
  rw [valAC, hxy, PairAlg.mul]
  have hx0 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c0) := hx.reg.c0
  have hx1 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c1) := hx.reg.c1
  have hy0 : RegularAt r (mapRatFunc ιL_K5 (coordsAC y).c0) := hy.reg.c0
  have hy1 : RegularAt r (mapRatFunc ιL_K5 (coordsAC y).c1) := hy.reg.c1
  have hbW : RegularAt r (mapRatFunc ιL_K5 (toRat k5Params.bW)) := by
    rw [mapRatFunc_algebraMap]; exact RegularAt.polynomial r _
  have hcW : RegularAt r (mapRatFunc ιL_K5 (toRat k5Params.cW)) := by
    rw [mapRatFunc_algebraMap]; exact RegularAt.polynomial r _
  simp only [map_add, map_sub, map_mul]
  rw [valueAt_mul_of_regularAt hx0 hy0, valueAt_mul_of_regularAt hx0 hy1,
    valueAt_mul_of_regularAt hx1 hy0,
    valueAt_mul_of_regularAt (regAt_mul_local hx1 hy1) hcW,
    valueAt_mul_of_regularAt (regAt_mul_local hx1 hy1) hbW,
    valueAt_mul_of_regularAt hx1 hy1]
  simp only [mapRatFunc_algebraMap, valueAt_polynomial]
  have h1 := hx.eq; have h2 := hy.eq; dsimp only [valAC] at h1 h2
  rw [← h1, ← h2]
  linear_combination -valueAt r (mapRatFunc ιL_K5 (coordsAC x).c1) *
    valueAt r (mapRatFunc ιL_K5 (coordsAC y).c1) * hW

private lemma valAC_pow {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {x : A_C} {vx : CoverL} (hx : ValAC r w x vx) (n : ℕ) :
    ValAC r w (x ^ n) (vx ^ n) := by
  induction n with
  | zero => simpa using valAC_one r w
  | succ k ih => rw [pow_succ, pow_succ]; exact valAC_mul hW ih hx

private lemma valAC_div_of_reg {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {x y : A_C} {vx vy : CoverL}
    (hx : ValAC r w x vx) (hy : ValAC r w y vy) (hreg : RegAC r (x / y)) (hvy : vy ≠ 0) :
    ValAC r w (x / y) (vx / vy) := by
  refine ⟨hreg, ?_⟩
  have hy_ne : y ≠ 0 := by
    intro h0; subst h0
    have := hy.eq.symm.trans (valAC_zero r w).eq
    exact hvy this
  have hmul : valAC r w (x / y) * vy = vx := by
    have h := (valAC_mul hW ⟨hreg, rfl⟩ hy).eq
    rw [div_mul_cancel₀ x hy_ne, hx.eq] at h
    exact h.symm
  exact (eq_div_iff hvy).mpr hmul

private lemma valAC_div_nat {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {x : A_C} {vx : CoverL} (hx : ValAC r w x vx) (n : ℕ) [hn2 : n.AtLeastTwo] :
    ValAC r w (x / OfNat.ofNat n) (vx / OfNat.ofNat n) := by
  have hn : (OfNat.ofNat n : CoverL) ≠ 0 := by
    change (n : CoverL) ≠ 0
    exact Nat.cast_ne_zero.mpr (by have := hn2.prop; omega)
  exact valAC_div_of_reg hW hx (valAC_ofNat r w n) (regAC_div_ofNat hx.reg n hn) hn

private lemma valAC_P18_z_AC {r w : CoverL}
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hw0 : w ≠ 0)
    (hcb : (k5Params.cb_h.map ιL_K5).eval r ≠ 0)
    (hnmWU : (k5Params.nm_WU.map ιL_K5).eval r ≠ 0)
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {z : A_C} {vz : CoverL} (hz : ValAC r w z vz) :
    ValAC r w (P18_z_AC z)
      (SheetCalculus.P18_of (SL (L := CoverL)) QL TL xL yL
        (vz / w) (-(pU ιL_K5 k5Params.ca_h r * vz + pUW ιL_K5 k5Params.c0W r w) / (w * pU ιL_K5 k5Params.cb_h r))
        r (w / r)) := by
  have hS : ValAC r w (ιC_K5 S_K) SL := valAC_ιC_K5 r w S_K
  have hQ : ValAC r w (ιC_K5 Q_K) QL := valAC_ιC_K5 r w Q_K
  have hT : ValAC r w (ιC_K5 T_K) TL := valAC_ιC_K5 r w T_K
  have hx : ValAC r w (ιC_K5 x_K) xL := valAC_ιC_K5 r w x_K
  have hy : ValAC r w (ιC_K5 y_K) yL := valAC_ιC_K5 r w y_K
  have hU : ValAC r w U_C r := valAC_U_C r w
  have hW_v : ValAC r w W_C w := valAC_W_C r w
  have hV : ValAC r w V_C (w / r) :=
    valAC_div_of_reg hW hW_v hU (regAC_V_C hr0) hr0
  have hV_ne : w / r ≠ 0 := div_ne_zero hw0 hr0
  have hu_ne : u_of r ≠ 0 := by
    rw [u_of]; exact div_ne_zero (sub_ne_zero.mpr hr1) (by exact_mod_cast (by decide : (9 : ℕ) ≠ 0))
  have hv_ne : v_of (w / r) ≠ 0 := by
    rw [v_of]
    refine div_ne_zero (sub_ne_zero.mpr ?_) (by exact_mod_cast (by decide : (9 : ℕ) ≠ 0))
    intro hwr
    have hw_eq : w = r := by rw [div_eq_one_iff_eq hr0] at hwr; exact hwr
    have hnm0 : (k5Params.nm_WU.map ιL_K5).eval r = 0 := by
      simp only [CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm, Polynomial.map_add,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
        Polynomial.map_X, Polynomial.map_one, eval_add, eval_sub, eval_mul, eval_pow,
        eval_neg, eval_X, eval_one]
      rw [hw_eq] at hW; linear_combination hW
    exact hnmWU hnm0
  have ha : ValAC r w (z / W_C) (vz / w) :=
    valAC_div_of_reg hW hz hW_v (regAC_div_W_C hz.reg hr0) hw0
  have hb_reg : RegAC r (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)) := by
    rw [← div_div]
    exact regAC_div_polyC (regAC_div_W_C (regAC_neg (regAC_add
      (regAC_mul (regAC_polyC r _) hz.reg) (regAC_pairC r _))) hr0) hcb
  have hb : ValAC r w
      (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
      (-(pU ιL_K5 k5Params.ca_h r * vz + pUW ιL_K5 k5Params.c0W r w) / (w * pU ιL_K5 k5Params.cb_h r)) :=
    valAC_div_of_reg hW
      (valAC_neg (valAC_add (valAC_mul hW (valAC_polyC r w _) hz) (valAC_pairC r w _)))
      (valAC_mul hW hW_v (valAC_polyC r w _)) hb_reg (mul_ne_zero hw0 hcb)
  set aC := z / W_C
  set bC := -(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)
  set aL := vz / w
  set bL := -(pU ιL_K5 k5Params.ca_h r * vz + pUW ιL_K5 k5Params.c0W r w) / (w * pU ιL_K5 k5Params.cb_h r)
  set ξSC := ιC_K5 S_K - aC * ιC_K5 T_K; set ξQC := ιC_K5 Q_K - bC * ιC_K5 T_K
  set ξSL := SL - aL * TL; set ξQL := QL - bL * TL
  have hξS : ValAC r w ξSC ξSL := valAC_sub hS (valAC_mul hW ha hT)
  have hξQ : ValAC r w ξQC ξQL := valAC_sub hQ (valAC_mul hW hb hT)
  have hmul {x y : A_C} {vx vy : CoverL} := @valAC_mul r w hW x y vx vy
  have hpow {x : A_C} {vx : CoverL} := @valAC_pow r w hW x vx
  have hdivn {x : A_C} {vx : CoverL} (hx : ValAC r w x vx) (n : ℕ) [n.AtLeastTwo] := valAC_div_nat hW hx n
  have hdHS : ∀ {s q : A_C} {vs vq : CoverL}, ValAC r w s vs → ValAC r w q vq →
      ValAC r w (dH_dS s q U_C V_C) (dH_dS vs vq r (w / r)) := fun hs hq => by
    dsimp only [dH_dS]
    repeat (with_reducible (first | exact hs | exact hq | exact hU | exact hV | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hdHQ : ∀ {s q v0 : A_C} {vs vq vv0 : CoverL}, ValAC r w s vs → ValAC r w q vq →
      ValAC r w v0 vv0 → ValAC r w (dH_dQ s q v0 U_C V_C) (dH_dQ vs vq vv0 r (w / r)) := fun hs hq hv0 => by
    dsimp only [dH_dQ]
    repeat (with_reducible (first | exact hs | exact hq | exact hv0 | exact hU | exact hV | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hnumM (mi : Fin 10) : ValAC r w (numM mi aC bC ξSC ξQC U_C V_C) (numM mi aL bL ξSL ξQL r (w / r)) := by
    have ha2 : ValAC r w (q1_a2 aC bC U_C V_C) (q1_a2 aL bL r (w / r)) := hdHS ha hb
    have ha0 : ValAC r w (q1_a0 ξSC ξQC U_C V_C) (q1_a0 ξSL ξQL r (w / r)) := hdHS hξS hξQ
    have ha1 : ValAC r w (q1_a1 aC bC ξSC ξQC U_C V_C) (q1_a1 aL bL ξSL ξQL r (w / r)) :=
      valAC_sub (valAC_sub (hdHS (valAC_add ha hξS) (valAC_add hb hξQ)) ha2) ha0
    have hb2 : ValAC r w (q2_b2 aC bC U_C V_C) (q2_b2 aL bL r (w / r)) := hdHQ ha hb (valAC_zero r w)
    have hb0 : ValAC r w (q2_b0 ξSC ξQC U_C V_C) (q2_b0 ξSL ξQL r (w / r)) := hdHQ hξS hξQ (valAC_one r w)
    have hb1 : ValAC r w (q2_b1 aC bC ξSC ξQC U_C V_C) (q2_b1 aL bL ξSL ξQL r (w / r)) := by
      have h00 := hdHQ (valAC_add ha hξS) (valAC_add hb hξQ) (valAC_zero r w)
      have h01 := hdHQ hξS hξQ (valAC_zero r w)
      exact valAC_add (valAC_sub (valAC_sub h00 hb2) h01)
        (hmul (hmul (hmul (hdivn (valAC_ofNat r w 10) 7) hb) hU) hV)
    have hd20 := valAC_sub (hmul ha2 hb0) (hmul ha0 hb2)
    have hd21 := valAC_sub (hmul ha2 hb1) (hmul ha1 hb2)
    have hd10 := valAC_sub (hmul ha1 hb0) (hmul ha0 hb1)
    have hcomb {m2 m1 m0 : A_C} {v2 v1 v0 : CoverL}
        (hm2 : ValAC r w m2 v2) (hm1 : ValAC r w m1 v1) (hm0 : ValAC r w m0 v0) :=
      hmul (hdivn (valAC_one r w) 16)
        (valAC_add (valAC_sub (hmul hm2 hd10) (hmul hm1 hd20)) (hmul hm0 hd21))
    fin_cases mi
    · exact hcomb (hpow ha 2) (hmul (hmul (valAC_ofNat r w 2) ha) hξS) (hpow hξS 2)
    · exact hcomb (hmul ha hb) (valAC_add (hmul ha hξQ) (hmul hb hξS)) (hmul hξS hξQ)
    · exact hcomb (hpow hb 2) (hmul (hmul (valAC_ofNat r w 2) hb) hξQ) (hpow hξQ 2)
    · exact hcomb ha hξS (valAC_zero r w)
    · exact hcomb (valAC_zero r w) ha hξS
    · exact hcomb hb hξQ (valAC_zero r w)
    · exact hcomb (valAC_zero r w) hb hξQ
    · exact hcomb (valAC_one r w) (valAC_zero r w) (valAC_zero r w)
    · exact hcomb (valAC_zero r w) (valAC_one r w) (valAC_zero r w)
    · exact hcomb (valAC_zero r w) (valAC_zero r w) (valAC_one r w)
  have hA0U : ValAC r w (A_0U aC bC ξSC ξQC U_C V_C) (A_0U aL bL ξSL ξQL r (w / r)) := by
    dsimp only [A_0U]
    repeat (with_reducible (first | exact hnumM _ | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hA0V : ValAC r w (A_0V aC bC ξSC ξQC U_C V_C) (A_0V aL bL ξSL ξQL r (w / r)) := by
    dsimp only [A_0V]
    repeat (with_reducible (first | exact hnumM _ | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hAY : ValAC r w (A_Y aC bC ξSC ξQC U_C V_C) (A_Y aL bL ξSL ξQL r (w / r)) := by
    dsimp only [A_Y]
    repeat (with_reducible (first | exact hU | exact hV | exact hnumM _ | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hAX : ValAC r w (A_X aC bC ξSC ξQC U_C V_C) (A_X aL bL ξSL ξQL r (w / r)) := by
    dsimp only [A_X]
    repeat (with_reducible (first | exact hU | exact hnumM _ | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hM0 : ValAC r w (A_0U aC bC ξSC ξQC U_C V_C / U_C + A_0V aC bC ξSC ξQC U_C V_C / V_C)
      (A_0U aL bL ξSL ξQL r (w / r) / r + A_0V aL bL ξSL ξQL r (w / r) / (w / r)) :=
    valAC_add (valAC_div_of_reg hW hA0U hU (regAC_div_U_C hA0U.reg hr0) hr0)
      (valAC_div_of_reg hW hA0V hV (regAC_div_V_C hA0V.reg hr0) hV_ne)
  have hu : ValAC r w (u_of U_C) (u_of r) := hdivn (valAC_sub hU (valAC_one r w)) 9
  have hv : ValAC r w (v_of V_C) (v_of (w / r)) := hdivn (valAC_sub hV (valAC_one r w)) 9
  have hH0 : ValAC r w (H0_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)) (H0_of SL QL TL) := by
    dsimp only [H0_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hT | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hdH0 (k : Fin 3) : ValAC r w (dH0_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)) (dH0_fn k SL QL TL) := by
    fin_cases k <;> dsimp only [dH0_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hT | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hdF5 (k : Fin 5) : ValAC r w (dF5_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K))
      (dF5_fn k SL QL TL xL yL) := by
    fin_cases k <;> dsimp only [dF5_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hT | exact hx | exact hy | exact hdH0 _ | exact valAC_ofNat r w _ | apply valAC_add | apply hmul | apply hpow))
  have hu3 : ValAC r w (u3_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) (u3_of SL QL xL) := by
    dsimp only [u3_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hx | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply hmul))
  have hv3 : ValAC r w (v3_of (ιC_K5 T_K) (ιC_K5 y_K)) (v3_of TL yL) := by
    dsimp only [v3_of]
    repeat (with_reducible (first | exact hT | exact hy | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub))
  have hDX2 : ValAC r w (DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) (DX2_of SL QL xL) := by
    dsimp only [DX2_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hu3 | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply hmul | apply hpow))
  have hDY2 : ValAC r w (DY2_of (ιC_K5 T_K) (ιC_K5 y_K)) (DY2_of TL yL) := by
    dsimp only [DY2_of]
    repeat (with_reducible (first | exact hT | exact hv3 | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply hmul | apply hpow))
  have hW2 : ValAC r w (W2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K))
      (W2_of SL QL TL xL yL) := hmul (hmul (hmul hS hT) hDX2) hDY2
  have hLX : ValAC r w (LX_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) U_C) (LX_of SL QL xL r) := by
    dsimp only [LX_of]
    repeat (with_reducible (first | exact hu | exact hS | exact hQ | exact hu3 | exact hU | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply hmul))
  have hLY : ValAC r w (LY_of (ιC_K5 T_K) (ιC_K5 y_K) V_C) (LY_of TL yL (w / r)) := by
    dsimp only [LY_of]
    repeat (with_reducible (first | exact hv | exact hT | exact hv3 | exact hV | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply hmul))
  have hdLX (k : Fin 5) : ValAC r w (dLX_fn k U_C) (dLX_fn k r) := by
    fin_cases k <;> dsimp only [dLX_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hu | exact hU | exact valAC_zero r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hdLY (k : Fin 5) : ValAC r w (dLY_fn k V_C) (dLY_fn k (w / r)) := by
    fin_cases k <;> dsimp only [dLY_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hv | exact hV | exact valAC_zero r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_neg | apply hmul))
  have hbr (k : Fin 5) : ValAC r w (br_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C)
      (br_fn k SL QL TL xL yL r (w / r)) := by
    dsimp only [br_fn]
    refine valAC_add ?_ (hmul (hmul (hmul (valAC_ofNat r w 2) hS) hT)
      (valAC_sub (hmul hLX (hdLY k)) (hmul hLY (hdLX k))))
    fin_cases k
    · exact hmul (hmul (valAC_neg hT) hLX) hLY
    · exact valAC_zero r w
    · exact hmul (hmul hS hLX) hLY
    · exact valAC_zero r w
    · exact valAC_zero r w
  have hdDX2 (k : Fin 5) : ValAC r w (dDX2_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) (dDX2_fn k SL QL xL) := by
    fin_cases k <;> dsimp only [dDX2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hu3 | exact valAC_zero r w | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hdDY2 (k : Fin 5) : ValAC r w (dDY2_fn k (ιC_K5 T_K) (ιC_K5 y_K)) (dDY2_fn k TL yL) := by
    fin_cases k <;> dsimp only [dDY2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hT | exact hv3 | exact valAC_zero r w | exact valAC_one r w | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hFc (f2 : Fin 5 → Fin 5 → A_C) (v2 : Fin 5 → Fin 5 → CoverL)
      (hf2 : ∀ i j, ValAC r w (f2 i j) (v2 i j)) (i : Fin 3) :
      ValAC r w (F_contract (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) f2 i)
        (F_contract SL QL TL xL yL v2 i) := by
    fin_cases i <;> dsimp only [F_contract, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      exact valAC_add (valAC_add (hmul (hdF5 4) (hf2 _ 3)) (hmul (hdF5 3) (hf2 4 _))) (hmul (hdF5 _) (hf2 3 4))
  have hdot (v : Fin 3 → A_C) (vl : Fin 3 → CoverL) (hv_v : ∀ i, ValAC r w (v i) (vl i)) :
      ValAC r w (dot_ab v aC bC) (dot_ab vl aL bL) :=
    valAC_add (valAC_add (hmul (hv_v 0) ha) (hmul (hv_v 1) hb)) (hv_v 2)
  have hom (i j : Fin 5) : ValAC r w (om_fn i j (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C)
      (om_fn i j SL QL TL xL yL r (w / r)) := by
    dsimp only [om_fn]
    have homX (k : Fin 5) : ValAC r w
        (match k with
         | 0 => -25 * ιC_K5 S_K * U_C + 15 * ιC_K5 Q_K * U_C + 9 * ιC_K5 x_K * U_C + 25 * ιC_K5 S_K - 15 * ιC_K5 Q_K
         | 1 => 30 * (U_C - 1) * ιC_K5 S_K
         | 3 => 18 * U_C * ιC_K5 S_K
         | _ => 0)
        (match k with
         | 0 => -25 * SL * r + 15 * QL * r + 9 * xL * r + 25 * SL - 15 * QL
         | 1 => 30 * (r - 1) * SL
         | 3 => 18 * r * SL
         | _ => 0) := by
      rcases k with ⟨_ | _ | _ | _ | _ | k, hk⟩
      · change ValAC r w (-25 * ιC_K5 S_K * U_C + 15 * ιC_K5 Q_K * U_C + 9 * ιC_K5 x_K * U_C + 25 * ιC_K5 S_K - 15 * ιC_K5 Q_K)
            (-25 * SL * r + 15 * QL * r + 9 * xL * r + 25 * SL - 15 * QL)
        repeat (with_reducible (first | exact hS | exact hQ | exact hx | exact hU | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
      · change ValAC r w (30 * (U_C - 1) * ιC_K5 S_K) (30 * (r - 1) * SL)
        repeat (with_reducible (first | exact hS | exact hU | exact valAC_one r w | exact valAC_ofNat r w _ | apply valAC_sub | apply hmul))
      · exact valAC_zero r w
      · change ValAC r w (18 * U_C * ιC_K5 S_K) (18 * r * SL)
        exact hmul (hmul (valAC_ofNat r w 18) hU) hS
      · exact valAC_zero r w
      · omega
    have homY (k : Fin 5) : ValAC r w
        (match k with
         | 2 => -25 * ιC_K5 T_K * V_C + 9 * ιC_K5 y_K * V_C + 25 * ιC_K5 T_K + 15 * V_C - 15
         | 4 => 18 * V_C * ιC_K5 T_K
         | _ => 0)
        (match k with
         | 2 => -25 * TL * (w / r) + 9 * yL * (w / r) + 25 * TL + 15 * (w / r) - 15
         | 4 => 18 * (w / r) * TL
         | _ => 0) := by
      rcases k with ⟨_ | _ | _ | _ | _ | k, hk⟩
      · exact valAC_zero r w
      · exact valAC_zero r w
      · change ValAC r w (-25 * ιC_K5 T_K * V_C + 9 * ιC_K5 y_K * V_C + 25 * ιC_K5 T_K + 15 * V_C - 15)
            (-25 * TL * (w / r) + 9 * yL * (w / r) + 25 * TL + 15 * (w / r) - 15)
        repeat (with_reducible (first | exact hT | exact hy | exact hV | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
      · exact valAC_zero r w
      · change ValAC r w (18 * V_C * ιC_K5 T_K) (18 * (w / r) * TL)
        exact hmul (hmul (valAC_ofNat r w 18) hV) hT
      · omega
    exact hmul (hdivn (valAC_one r w) 81) (valAC_sub (hmul (homX i) (homY j)) (hmul (homX j) (homY i)))
  have hA1 : ValAC r w (A1_of (ιC_K5 S_K) (ιC_K5 Q_K) U_C V_C) (A1_of SL QL r (w / r)) := by
    dsimp only [A1_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hU | exact hV | exact valAC_one r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_sub | apply hmul | apply hpow))
  have hB1 : ValAC r w (B1_of (ιC_K5 T_K) U_C V_C) (B1_of TL r (w / r)) := by
    dsimp only [B1_of]
    repeat (with_reducible (first | exact hT | exact hU | exact hV | exact valAC_one r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_sub | apply hmul | apply hpow))
  have hdA1 (k : Fin 3) : ValAC r w (dA1_fn k (ιC_K5 S_K) (ιC_K5 Q_K) U_C V_C) (dA1_fn k SL QL r (w / r)) := by
    fin_cases k <;> dsimp only [dA1_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hU | exact hV | exact valAC_zero r w | exact valAC_one r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hQY : ValAC r w (dot_ab (QY_num (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) aC bC)
      (dot_ab (QY_num SL QL TL xL yL r (w / r)) aL bL) :=
    hdot _ _ (fun i => hmul hDY2 (valAC_sub
      (hmul hDX2 (hFc _ _ (fun p q => hmul (hmul hS hT) (hom p q)) i))
      (hFc _ _ (fun p q => hmul (hmul hS hT) (valAC_sub (hmul (hdDX2 p) (hbr q)) (hmul (hdDX2 q) (hbr p)))) i)))
  have hQX : ValAC r w (dot_ab (QX_num (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) aC bC)
      (dot_ab (QX_num SL QL TL xL yL r (w / r)) aL bL) :=
    hdot _ _ (fun i => hmul hDX2 (valAC_add
      (hmul (valAC_neg hDY2) (hFc _ _ (fun p q => hmul (hmul hS hT) (hom p q)) i))
      (hFc _ _ (fun p q => hmul (hmul hS hT) (valAC_sub (hmul (hdDY2 p) (hbr q)) (hmul (hdDY2 q) (hbr p)))) i)))
  have hcA1 : ValAC r w (cA1_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) aC bC U_C V_C)
      (cA1_of SL QL TL aL bL r (w / r)) := by
    dsimp only [cA1_of]
    repeat (with_reducible (first | exact hH0 | exact hA1 | exact ha | exact hb | exact hdA1 _ | exact hdH0 _ | apply valAC_add | apply valAC_sub | apply hmul))
  have hEB : ValAC r w (EB_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C)
      (EB_of SL QL TL xL yL r (w / r)) := by
    dsimp only [EB_of]
    repeat (with_reducible (first | exact hW2 | exact hdF5 _ | exact hbr _ | exact valAC_ofNat r w _ | apply valAC_sub | apply hmul))
  have hqY := valAC_div_of_reg hW hQY hv (regAC_div_v_of hQY.reg hnmWU) hv_ne
  have hqX := valAC_div_of_reg hW hQX hu (regAC_div_u_of hQX.reg hr1) hu_ne
  have hcA1_v := valAC_div_of_reg hW hcA1 hv (regAC_div_v_of hcA1.reg hnmWU) hv_ne
  unfold P18_z_AC P18_of
  exact valAC_add (hmul hM0 (valAC_add (valAC_add
    (hmul (hmul hH0 hA1) hqY) (hmul (hmul hH0 hB1) hqX)) (hmul hcA1_v hEB)))
    (hmul (valAC_add (hmul hAY hqY) (hmul hAX hqX)) (hpow hH0 2))

private lemma valAC_interp4 {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {f : A_C → A_C} {g : CoverL → CoverL}
    (hf : ∀ {z : A_C} {vz : CoverL}, ValAC r w z vz → ValAC r w (f z) (g vz)) :
    let p := interp4 f; let q := interp4 g
    ValAC r w p.1 q.1 ∧ ValAC r w p.2.1 q.2.1 ∧ ValAC r w p.2.2.1 q.2.2.1 ∧
    ValAC r w p.2.2.2.1 q.2.2.2.1 ∧ ValAC r w p.2.2.2.2 q.2.2.2.2 := by
  have h0 := hf (valAC_zero r w)
  have h1 := hf (valAC_one r w)
  have hm1 := hf (valAC_neg (valAC_one r w))
  have h2 := hf (valAC_ofNat r w 2)
  have hm2 := hf (valAC_neg (valAC_ofNat r w 2))
  have hmul {x y : A_C} {vx vy : CoverL} := @valAC_mul r w hW x y vx vy
  have hdivn {x : A_C} {vx : CoverL} (hx : ValAC r w x vx) (n : ℕ) [n.AtLeastTwo] := valAC_div_nat hW hx n
  dsimp only [interp4]
  refine ⟨?_, ?_, ?_, ?_, h0⟩
  · exact hdivn (valAC_add (valAC_add (hmul (valAC_neg (valAC_ofNat r w 4)) (valAC_add h1 hm1))
      (valAC_add h2 hm2)) (hmul (valAC_ofNat r w 6) h0)) 24
  · exact hdivn (valAC_add (hmul (valAC_neg (valAC_ofNat r w 2)) (valAC_sub h1 hm1))
      (valAC_sub h2 hm2)) 12
  · exact hdivn (valAC_sub (valAC_sub (hmul (valAC_ofNat r w 16) (valAC_add h1 hm1))
      (valAC_add h2 hm2)) (hmul (valAC_ofNat r w 30) h0)) 24
  · exact hdivn (valAC_sub (hmul (valAC_ofNat r w 8) (valAC_sub h1 hm1))
      (valAC_sub h2 hm2)) 12

private lemma valAC_remDeg4 {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {q2 q1 q0 p4 p3 p2 p1 p0 : A_C} {vq2 vq1 vq0 vp4 vp3 vp2 vp1 vp0 : CoverL}
    (hq2 : ValAC r w q2 vq2) (hq1 : ValAC r w q1 vq1) (hq0 : ValAC r w q0 vq0)
    (hp4 : ValAC r w p4 vp4) (hp3 : ValAC r w p3 vp3) (hp2 : ValAC r w p2 vp2)
    (hp1 : ValAC r w p1 vp1) (hp0 : ValAC r w p0 vp0) :
    ValAC r w (remDeg4_P1 q2 q1 q0 p4 p3 p2 p1) (remDeg4_P1 vq2 vq1 vq0 vp4 vp3 vp2 vp1) ∧
    ValAC r w (remDeg4_P0 q2 q1 q0 p4 p3 p2 p0) (remDeg4_P0 vq2 vq1 vq0 vp4 vp3 vp2 vp0) := by
  have hmul {x y : A_C} {vx vy : CoverL} := @valAC_mul r w hW x y vx vy
  have hpow {x : A_C} {vx : CoverL} := @valAC_pow r w hW x vx
  have hr3 := valAC_sub (hmul hq2 hp3) (hmul hq1 hp4)
  have hr2 := valAC_sub (hmul hq2 hp2) (hmul hq0 hp4)
  have hs2 := valAC_sub (hmul hq2 hr2) (hmul hq1 hr3)
  have hs1 := valAC_sub (hmul (hpow hq2 2) hp1) (hmul hq0 hr3)
  exact ⟨valAC_sub (hmul hq2 hs1) (hmul hq1 hs2),
         valAC_sub (hmul (hpow hq2 3) hp0) (hmul hq0 hs2)⟩

end BranchEvalProof

end SymmetricSexticResidual.CoverResidue

theorem solution :
    (∀ {r w : SymmetricSexticResidual.CoverResidue.CoverL},
      r ≠ 0 → r ≠ 1 → w ≠ 0 →
      (SymmetricSexticResidual.CoverAlgebra.k5Params.cb_h.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r ≠ 0 →
      (SymmetricSexticResidual.CoverAlgebra.k5Params.nm_WU.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r ≠ 0 →
      w ^ 2 + (SymmetricSexticResidual.CoverAlgebra.k5Params.bW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r * w +
        (SymmetricSexticResidual.CoverAlgebra.k5Params.cW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r = 0 →
      ∀ {z : SymmetricSexticResidual.CoverResidue.A_C} {vz : SymmetricSexticResidual.CoverResidue.CoverL},
      SymmetricSexticResidual.CoverResidue.ValAC r w z vz →
      SymmetricSexticResidual.CoverResidue.ValAC r w (SymmetricSexticResidual.CoverResidue.P18_z_AC z)
        (SymmetricSexticResidual.SheetCalculus.P18_of
          (SymmetricSexticResidual.SheetCalculus.SL (L := SymmetricSexticResidual.CoverResidue.CoverL))
          SymmetricSexticResidual.SheetCalculus.QL SymmetricSexticResidual.SheetCalculus.TL
          SymmetricSexticResidual.SheetCalculus.xL SymmetricSexticResidual.SheetCalculus.yL
          (vz / w)
          (-(SymmetricSexticResidual.CoverResidue.pU SymmetricSexticResidual.CoverResidue.ιL_K5
              SymmetricSexticResidual.CoverAlgebra.k5Params.ca_h r * vz +
            SymmetricSexticResidual.CoverResidue.pUW SymmetricSexticResidual.CoverResidue.ιL_K5
              SymmetricSexticResidual.CoverAlgebra.k5Params.c0W r w) /
            (w * SymmetricSexticResidual.CoverResidue.pU SymmetricSexticResidual.CoverResidue.ιL_K5
              SymmetricSexticResidual.CoverAlgebra.k5Params.cb_h r))
          r (w / r))) ∧
    (∀ {r w : SymmetricSexticResidual.CoverResidue.CoverL},
      w ^ 2 + (SymmetricSexticResidual.CoverAlgebra.k5Params.bW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r * w +
        (SymmetricSexticResidual.CoverAlgebra.k5Params.cW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r = 0 →
      ∀ {f : SymmetricSexticResidual.CoverResidue.A_C → SymmetricSexticResidual.CoverResidue.A_C}
        {g : SymmetricSexticResidual.CoverResidue.CoverL → SymmetricSexticResidual.CoverResidue.CoverL},
      (∀ {z : SymmetricSexticResidual.CoverResidue.A_C} {vz : SymmetricSexticResidual.CoverResidue.CoverL},
        SymmetricSexticResidual.CoverResidue.ValAC r w z vz →
        SymmetricSexticResidual.CoverResidue.ValAC r w (f z) (g vz)) →
      let p := QuadraticCovers.interp4 f; let q := QuadraticCovers.interp4 g
      SymmetricSexticResidual.CoverResidue.ValAC r w p.1 q.1 ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w p.2.1 q.2.1 ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w p.2.2.1 q.2.2.1 ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w p.2.2.2.1 q.2.2.2.1 ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w p.2.2.2.2 q.2.2.2.2) ∧
    (∀ {r w : SymmetricSexticResidual.CoverResidue.CoverL},
      w ^ 2 + (SymmetricSexticResidual.CoverAlgebra.k5Params.bW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r * w +
        (SymmetricSexticResidual.CoverAlgebra.k5Params.cW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r = 0 →
      ∀ {q2 q1 q0 p4 p3 p2 p1 p0 : SymmetricSexticResidual.CoverResidue.A_C}
        {vq2 vq1 vq0 vp4 vp3 vp2 vp1 vp0 : SymmetricSexticResidual.CoverResidue.CoverL},
      SymmetricSexticResidual.CoverResidue.ValAC r w q2 vq2 →
      SymmetricSexticResidual.CoverResidue.ValAC r w q1 vq1 →
      SymmetricSexticResidual.CoverResidue.ValAC r w q0 vq0 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p4 vp4 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p3 vp3 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p2 vp2 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p1 vp1 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p0 vp0 →
      SymmetricSexticResidual.CoverResidue.ValAC r w
        (QuadraticCovers.remDeg4_P1 q2 q1 q0 p4 p3 p2 p1)
        (QuadraticCovers.remDeg4_P1 vq2 vq1 vq0 vp4 vp3 vp2 vp1) ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w
        (QuadraticCovers.remDeg4_P0 q2 q1 q0 p4 p3 p2 p0)
        (QuadraticCovers.remDeg4_P0 vq2 vq1 vq0 vp4 vp3 vp2 vp0)) :=
  ⟨@SymmetricSexticResidual.CoverResidue.valAC_P18_z_AC,
   @SymmetricSexticResidual.CoverResidue.valAC_interp4,
   @SymmetricSexticResidual.CoverResidue.valAC_remDeg4⟩
