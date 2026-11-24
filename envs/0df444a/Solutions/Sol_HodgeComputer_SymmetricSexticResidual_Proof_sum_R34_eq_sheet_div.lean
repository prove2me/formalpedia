-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.sum_R34_eq_sheet_div
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T09:38:48.162849+00:00
-- url     : https://prove2.me/submissions/5b26cd1d-b1f7-4974-863e-033fdc380d92

import Definitions.Def_HodgeComputerFormal_CoverResidues
import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_CoverFactors
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_det_J_fib_schur
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_sheet_horiz_identity
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_reg_identities
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_valAC_P18
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

private abbrev P18_of_isPolyDeg4 := @HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.P18_deg4
private abbrev E1_of_cover := @HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.E1_cover
private abbrev E2_z_of_cover := @HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.E2_z_cover
private abbrev E3_z_of_cover := @HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.E3_z_cover
private abbrev valAC_P18_z_AC := @HodgeComputer.SymmetricSexticResidual.Proof.cover_valAC_P18.1
private abbrev valAC_interp4 := @HodgeComputer.SymmetricSexticResidual.Proof.cover_valAC_P18.2.1
private abbrev valAC_remDeg4 := @HodgeComputer.SymmetricSexticResidual.Proof.cover_valAC_P18.2.2

section RegACBasic
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

end RegACBasic

private lemma polyC_81_Av0_Q5_eq :
    polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3) =
      81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q5_z ^ 3 := by
  simp only [polyC, ιC_K5, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, RingHom.comp_apply]
  rfl


section SplittingAndResidues
private lemma monic_quad_poly {F : Type*} [Field F] (b c : F) :
    (X ^ 2 + C b * X + C c : F[X]).Monic := by
  rw [add_assoc]
  apply (monic_X_pow 2).add_of_left
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))
  · exact lt_of_le_of_lt degree_C_le (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))

private lemma natDegree_quad_poly {F : Type*} [Field F] (b c : F) :
    (X ^ 2 + C b * X + C c : F[X]).natDegree = 2 := by
  rw [add_assoc]
  have hlt : (C b * X + C c : F[X]).natDegree < 2 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ (by simp))
    exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by simp)
  rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hlt), natDegree_X_pow]


/-- Above every `r ∈ R34`, the fiber quadratic `W^2 + bW(r)*W + cW(r)` splits in `CoverL`
into two distinct roots `w1 ≠ w2`. -/
lemma E0_splits_at_R34 (r : CoverL) (hr : r ∈ R34) :
    ∃ w1 w2 : CoverL,
      w1 + w2 = -(k5Params.bW.map ιL_K5).eval r ∧
      w1 * w2 = (k5Params.cW.map ιL_K5).eval r ∧
      w1 ≠ w2 := by
  have hr_eval : (P34_K5.map ιL_K5).eval r = 0 := mem_R34_iff.mp hr
  have hmem : ∃ r1 ∈ (P34_K5.map (algebraMap K5 L1)).roots.toFinset, algebraMap L1 CoverL r1 = r := by
    have hfac := P34_splits_L1.eq_prod_roots
    have hmap := congrArg (fun p : L1[X] => (p.map (algebraMap L1 CoverL)).eval r) hfac
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL, hr_eval] at hmap
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod,
      Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X,
      eval_mul, eval_C, eval_multiset_prod, eval_sub, eval_X] at hmap
    have hlc : algebraMap L1 CoverL (P34_K5.map (algebraMap K5 L1)).leadingCoeff ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap L1 CoverL).injective).mpr
        (leadingCoeff_ne_zero.mpr (Polynomial.map_ne_zero P34_K5_ne_zero))
    have hprod0 := (mul_eq_zero.mp hmap.symm).resolve_left hlc
    obtain ⟨r1, hr1, hr1_eq⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod0)
    exact ⟨r1, Multiset.mem_toFinset.mpr hr1, (sub_eq_zero.mp hr1_eq).symm⟩
  obtain ⟨r1, hr1_mem, hr1_eq⟩ := hmem
  let q1 : L1[X] := X ^ 2 + C ((k5Params.bW.map (algebraMap K5 L1)).eval r1) * X +
    C ((k5Params.cW.map (algebraMap K5 L1)).eval r1)
  have hdvd : q1 ∣ Q_quad := Finset.dvd_prod_of_mem _ hr1_mem
  have hq_map : q1.map (algebraMap L1 CoverL) =
      X ^ 2 + C ((k5Params.bW.map ιL_K5).eval r) * X + C ((k5Params.cW.map ιL_K5).eval r) := by
    have hev (P : K5[X]) : algebraMap L1 CoverL ((P.map (algebraMap K5 L1)).eval r1) = (P.map ιL_K5).eval r := by
      rw [← Polynomial.eval_map_apply, Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL, hr1_eq]
    simp only [q1, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X, hev]
  have hsplit : (q1.map (algebraMap L1 CoverL)).Splits :=
    (Polynomial.SplittingField.splits Q_quad).of_dvd (Polynomial.map_ne_zero Q_quad_ne_zero)
      (Polynomial.map_dvd (algebraMap L1 CoverL) hdvd)
  rw [hq_map] at hsplit
  set b := (k5Params.bW.map ιL_K5).eval r
  set c := (k5Params.cW.map ιL_K5).eval r
  have hcard : (X ^ 2 + C b * X + C c : CoverL[X]).roots.card = 2 := by
    rw [← hsplit.natDegree_eq_card_roots, natDegree_quad_poly]
  obtain ⟨w1, w2, hroots⟩ := Multiset.card_eq_two.mp hcard
  have hfac : X ^ 2 + C b * X + C c = (X - C w1) * (X - C w2) := by
    have hprod := hsplit.eq_prod_roots
    rw [hroots, (monic_quad_poly b c).leadingCoeff, map_one, one_mul] at hprod
    simpa [mul_assoc] using hprod
  have hfac' : X ^ 2 + C b * X + C c = X ^ 2 + C (-(w1 + w2)) * X + C (w1 * w2) := by
    rw [hfac]; simp only [map_neg, map_add, map_mul]; ring
  have hsum : w1 + w2 = -b := by
    have hc1 := congrArg (fun p : CoverL[X] => p.coeff 1) hfac'
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C] at hc1
    norm_num at hc1
    linear_combination hc1
  have hprod : w1 * w2 = c := by
    have hc0 := congrArg (fun p : CoverL[X] => p.coeff 0) hfac'
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C] at hc0
    norm_num at hc0
    exact hc0.symm
  have hsep : w1 ≠ w2 := by
    intro heq
    have hdisc_ne : (k5Params.disc_E0.map ιL_K5).eval r ≠ 0 :=
      eval_ne_zero_of_isCoprime isCoprime_P34_disc_E0 hr_eval
    have hdisc_eq : (k5Params.disc_E0.map ιL_K5).eval r = (w1 - w2) ^ 2 := by
      simp only [CoverParams.disc_E0, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
        Polynomial.map_ofNat, eval_sub, eval_pow, eval_mul, eval_ofNat]
      change b ^ 2 - 4 * c = (w1 - w2) ^ 2
      rw [← hprod, show b = -(w1 + w2) by linear_combination hsum]; ring
    rw [heq, sub_self, zero_pow (by omega)] at hdisc_eq
    exact hdisc_ne hdisc_eq
  exact ⟨w1, w2, hsum, hprod, hsep⟩

-- Dual-number evaluation helpers and pure-field directional derivatives along `(a', b', 1, V')`.
section DualCoverDeriv
variable {F : Type*} [Field F] [CharZero F] (φ : K5 →+* F)

private abbrev pU_d (P : K5[X]) (U : F) : F := (P.derivative.map φ).eval U
private abbrev pU_D (P : K5[X]) (U : F) : Dual F := P.eval₂ (Dual.C.comp φ) ⟨U, 1⟩
private abbrev pUW_D (x : PairAlg K5[X]) (U W W' : F) : Dual F :=
  PairAlg.evalAt ⟨W, W'⟩ (PairAlg.map (Polynomial.eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) x)

omit [CharZero F] in
private lemma pU_D_eq (P : K5[X]) (U : F) : pU_D φ P U = ⟨pU φ P U, pU_d φ P U⟩ := by
  rw [pU_D, ← Polynomial.eval₂_map, Dual.eval₂_eq, pU, pU_d, Polynomial.derivative_map, mul_one]

omit [CharZero F] in
private lemma pU_D_quadU (c0 c1 c2 : K5) (U : F) :
    pU_D φ (CoverParams.quadU c0 c1 c2) U =
      ⟨φ c0 + φ c1 * U + φ c2 * U ^ 2, φ c1 + 2 * φ c2 * U⟩ := by
  rw [pU_D_eq, pU, pU_d, CoverParams.quadU]
  ext
  · simp [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  · simp [derivative_add, derivative_mul, derivative_C, derivative_X]
    ring

omit [CharZero F] in
private lemma pU_D_add (P Q : K5[X]) (U : F) : pU_D φ (P + Q) U = pU_D φ P U + pU_D φ Q U :=
  map_add (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P Q
omit [CharZero F] in
private lemma pU_D_sub (P Q : K5[X]) (U : F) : pU_D φ (P - Q) U = pU_D φ P U - pU_D φ Q U :=
  map_sub (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P Q
omit [CharZero F] in
private lemma pU_D_neg (P : K5[X]) (U : F) : pU_D φ (-P) U = -pU_D φ P U :=
  map_neg (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P
omit [CharZero F] in
private lemma pU_D_mul (P Q : K5[X]) (U : F) : pU_D φ (P * Q) U = pU_D φ P U * pU_D φ Q U :=
  map_mul (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P Q
omit [CharZero F] in
private lemma pU_D_pow (P : K5[X]) (n : ℕ) (U : F) : pU_D φ (P ^ n) U = pU_D φ P U ^ n :=
  map_pow (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P n
omit [CharZero F] in
private lemma pU_D_C (c : K5) (U : F) : pU_D φ (C c) U = Dual.C (φ c) := by
  simp [pU_D]
omit [CharZero F] in
private lemma pU_D_X (U : F) : pU_D φ X U = ⟨U, 1⟩ := by
  simp [pU_D]
omit [CharZero F] in
private lemma pU_D_ofNat (n : ℕ) [n.AtLeastTwo] (U : F) :
    pU_D φ (OfNat.ofNat n) U = OfNat.ofNat n := by
  change eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩ (OfNat.ofNat n) = OfNat.ofNat n
  exact map_ofNat _ n

omit [CharZero F] in
private lemma pUW_D_val (x : PairAlg K5[X]) (U W W' : F) :
    (pUW_D φ x U W W').val = pUW φ x U W := by
  simp only [pUW_D, pUW, PairAlg.evalAt, PairAlg.map, Dual.add_val, Dual.mul_val,
    Polynomial.coe_eval₂RingHom, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom,
    RingHom.comp_apply]
  change (pU_D φ x.c0 U).val + (pU_D φ x.c1 U).val * W = pU φ x.c0 U + pU φ x.c1 U * W
  rw [pU_D_eq, pU_D_eq]

omit [CharZero F] in
private lemma pUW_D_add (x y : PairAlg K5[X]) (U W W' : F) :
    pUW_D φ (PairAlg.add x y) U W W' = pUW_D φ x U W W' + pUW_D φ y U W W' := by
  simp only [pUW_D, PairAlg.map_add, PairAlg.evalAt_add]
omit [CharZero F] in
private lemma pUW_D_sub (x y : PairAlg K5[X]) (U W W' : F) :
    pUW_D φ (PairAlg.sub x y) U W W' = pUW_D φ x U W W' - pUW_D φ y U W W' := by
  simp only [pUW_D, PairAlg.map_sub, PairAlg.evalAt_sub]
omit [CharZero F] in
private lemma pUW_D_smul (s : K5[X]) (x : PairAlg K5[X]) (U W W' : F) :
    pUW_D φ (PairAlg.smul s x) U W W' = pU_D φ s U * pUW_D φ x U W W' := by
  simp only [pUW_D, PairAlg.map_smul, PairAlg.evalAt_smul, Polynomial.coe_eval₂RingHom]
omit [CharZero F] in
private lemma pUW_D_ofScalar (s : K5[X]) (U W W' : F) :
    pUW_D φ (PairAlg.ofScalar s) U W W' = pU_D φ s U := by
  simp only [pUW_D, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, Polynomial.coe_eval₂RingHom]
omit [CharZero F] in
private lemma pUW_D_W (U W W' : F) : pUW_D φ PairAlg.W U W W' = ⟨W, W'⟩ := by
  simp only [pUW_D, PairAlg.map_W, PairAlg.evalAt_W]
omit [CharZero F] in
private lemma pUW_D_pmul (x y : PairAlg K5[X]) (U W W' : F)
    (hWD : (⟨W, W'⟩ : Dual F) ^ 2 + pU_D φ k5Params.bW U * ⟨W, W'⟩ + pU_D φ k5Params.cW U = 0) :
    pUW_D φ (k5Params.pmul x y) U W W' = pUW_D φ x U W W' * pUW_D φ y U W W' := by
  simp only [pUW_D, CoverParams.pmul, PairAlg.map_mul, Polynomial.coe_eval₂RingHom]
  exact PairAlg.evalAt_mul (pU_D φ k5Params.bW U) (pU_D φ k5Params.cW U) (⟨W, W'⟩ : Dual F) hWD _ _

omit [CharZero F] in
private lemma pUW_D_toUW (v0 v1 v2 : K5) (U W W' : F)
    (hWD : (⟨W, W'⟩ : Dual F) ^ 2 + pU_D φ k5Params.bW U * ⟨W, W'⟩ + pU_D φ k5Params.cW U = 0) :
    pUW_D φ (k5Params.toUW v0 v1 v2) U W W' =
      Dual.C (φ v2) * (⟨W, W'⟩ : Dual F) ^ 2 + Dual.C (φ v1) * (⟨U, 1⟩ : Dual F) * ⟨W, W'⟩ +
        Dual.C (φ v0) * (⟨U, 1⟩ : Dual F) ^ 2 := by
  unfold pUW_D CoverParams.toUW PairAlg.evalAt PairAlg.map
  simp only [Polynomial.coe_eval₂RingHom, map_sub, map_mul, map_pow, eval₂_C, eval₂_X, RingHom.comp_apply]
  change (Dual.C (φ v0) * (⟨U, 1⟩ : Dual F) ^ 2 - Dual.C (φ v2) * pU_D φ k5Params.cW U) +
    (Dual.C (φ v1) * (⟨U, 1⟩ : Dual F) - Dual.C (φ v2) * pU_D φ k5Params.bW U) * (⟨W, W'⟩ : Dual F) = _
  linear_combination -Dual.C (φ v2) * hWD

private lemma J_fib_03 (a b U W : F) (hU : U ≠ 0) :
    dE_dV 0 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      φ k5Params.Av0 * (2 * W + pU φ k5Params.bW U) := by
  have hT3 : φ T_K - 3 ≠ 0 := by
    have := (map_ne_zero_iff φ φ.injective).mpr T_K_sub_3_ne
    simpa only [map_sub, map_ofNat] using this
  simp only [dE_dV, dH_dV, pU, CoverParams.bW, CoverParams.Bv, CoverParams.quadU,
    CoverParams.Av0, CoverParams.Av0_inv, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2,
    CoverParams.inv4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
    k5Params_inv2, k5Params_inv3, k5Params_inv7, k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU, hT3]; ring

private lemma J_fib_10 (a b U W : F) (hU : U ≠ 0) :
    U * dE_da 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) = pU φ k5Params.ca_h U * W := by
  simp only [dE_da, dH_dS, pU, CoverParams.ca_h, CoverParams.quadU,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_S, k5Params_Q,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma J_fib_11 (a b U W : F) (hU : U ≠ 0) :
    U * dE_db 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) = pU φ k5Params.cb_h U * W := by
  simp only [dE_db, dH_dQ, pU, CoverParams.cb_h, CoverParams.quadU,
    CoverParams.inv9, CoverParams.inv27,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma J_fib_20 (a b U W : F) (hU : U ≠ 0) :
    U * dE_da 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      2 * pU φ k5Params.q20 U * (W * a) + pU φ k5Params.q11 U * (W * b) := by
  simp only [dE_da, dH_dS, pU, CoverParams.q20, CoverParams.q11, CoverParams.quadU,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_S, k5Params_Q,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma J_fib_21 (a b U W : F) (hU : U ≠ 0) :
    U * dE_db 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.q11 U * (W * a) + 2 * pU φ k5Params.q02 U * (W * b) := by
  simp only [dE_db, dH_dQ, pU, CoverParams.q11, CoverParams.q02, CoverParams.quadU,
    CoverParams.inv9, CoverParams.inv27,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma J_fib_minor12 (z U W : F) (hU : U ≠ 0) (hW0 : W ≠ 0) (hcb : pU φ k5Params.cb_h U ≠ 0) :
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    let M := J_fib (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)
    M 1 1 * M 2 0 - M 1 0 * M 2 1 =
      W * (2 * pUW φ k5Params.d2_2 U W * z + pUW φ k5Params.d2_1 U W) / (U ^ 2 * pU φ k5Params.cb_h U) := by
  intro a b M
  have h10 : U * M 1 0 = pU φ k5Params.ca_h U * W := J_fib_10 φ a b U W hU
  have h11 : U * M 1 1 = pU φ k5Params.cb_h U * W := J_fib_11 φ a b U W hU
  have h20 : U * M 2 0 = 2 * pU φ k5Params.q20 U * (W * a) + pU φ k5Params.q11 U * (W * b) :=
    J_fib_20 φ a b U W hU
  have h21 : U * M 2 1 = pU φ k5Params.q11 U * (W * a) + 2 * pU φ k5Params.q02 U * (W * b) :=
    J_fib_21 φ a b U W hU
  have hWa : W * a = z := mul_div_cancel₀ z hW0
  have hWb : pU φ k5Params.cb_h U * (W * b) = -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) := by
    dsimp only [b]; field_simp [hW0, hcb]
  have hd22 : pUW φ k5Params.d2_2 U W =
      pU φ k5Params.q20 U * pU φ k5Params.cb_h U ^ 2 -
      pU φ k5Params.q11 U * pU φ k5Params.ca_h U * pU φ k5Params.cb_h U +
      pU φ k5Params.q02 U * pU φ k5Params.ca_h U ^ 2 := by
    simp [pUW, CoverParams.d2_2, CoverParams.Q5_z, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, pU]
  have hd21 : pUW φ k5Params.d2_1 U W =
      (-pU φ k5Params.q11 U * pU φ k5Params.cb_h U + 2 * pU φ k5Params.q02 U * pU φ k5Params.ca_h U) *
      pUW φ k5Params.c0W U W := by
    simp [pUW, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul, pU]
  rw [hd22, hd21, eq_div_iff (mul_ne_zero (pow_ne_zero 2 hU) hcb)]
  have hmul : (M 1 1 * M 2 0 - M 1 0 * M 2 1) * (U ^ 2 * pU φ k5Params.cb_h U) =
      pU φ k5Params.cb_h U * ((U * M 1 1) * (U * M 2 0) - (U * M 1 0) * (U * M 2 1)) := by ring
  rw [hmul, h10, h11, h20, h21, hWa]
  linear_combination W * (pU φ k5Params.q11 U * pU φ k5Params.cb_h U -
    2 * pU φ k5Params.q02 U * pU φ k5Params.ca_h U) * hWb

private lemma dE0_along (a b U W W' : F) (hU : U ≠ 0) :
    E_fn 0 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * (dE_dU 0 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
      dE_dV 0 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * ((W' * U - W) / U ^ 2)) =
    (Dual.C (φ k5Params.Av0) *
      ((⟨W, W'⟩ : Dual F) ^ 2 + pU_D φ k5Params.bW U * (⟨W, W'⟩ : Dual F) + pU_D φ k5Params.cW U)).eps := by
  have hT3 : φ T_K - 3 ≠ 0 := by
    have := (map_ne_zero_iff φ φ.injective).mpr T_K_sub_3_ne
    simpa only [map_sub, map_ofNat] using this
  have hbW : pU_D φ k5Params.bW U =
      Dual.C (φ k5Params.Av0_inv) *
        ⟨φ k5Params.Bv0 + φ k5Params.Bv1 * U + φ k5Params.Bv2 * U ^ 2,
          φ k5Params.Bv1 + 2 * φ k5Params.Bv2 * U⟩ := by
    rw [CoverParams.bW, pU_D_mul, pU_D_C, CoverParams.Bv, pU_D_quadU]
  have hcW : pU_D φ k5Params.cW U =
      Dual.C (φ (k5Params.Cv0 * k5Params.Av0_inv)) * ⟨U ^ 2, 2 * U⟩ := by
    rw [CoverParams.cW, pU_D_mul, pU_D_C, pU_D_pow, pU_D_X, Dual.pow_eq]
    congr 1; ext <;> simp
  rw [hbW, hcW, Dual.pow_eq]
  simp only [Dual.mul_eps, Dual.add_eps, Dual.mul_val, Dual.add_val, Dual.C_val, Dual.C_eps]
  simp only [E_fn, dE_dU, dE_dV, H_cub, dH_dU, dH_dV,
    CoverParams.Av0, CoverParams.Av0_inv, CoverParams.Cv0, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2,
    CoverParams.inv4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
    k5Params_inv2, k5Params_inv3, k5Params_inv7, k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU, hT3]; ring

private lemma dE1_along (a b U W a' b' W' : F) (hU : U ≠ 0) :
    E_fn 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * (dE_da 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * a' +
      dE_db 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * b' +
      dE_dU 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
      dE_dV 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * ((W' * U - W) / U ^ 2)) =
    (pU_D φ k5Params.ca_h U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) +
      pU_D φ k5Params.cb_h U * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) +
      Dual.C (φ k5Params.c0_V2) * (⟨W, W'⟩ : Dual F) ^ 2 +
      Dual.C (φ k5Params.c0_V1) * (⟨U, 1⟩ : Dual F) * (⟨W, W'⟩ : Dual F) +
      Dual.C (φ k5Params.c0_V0) * (⟨U, 1⟩ : Dual F) ^ 2).eps := by
  rw [CoverParams.ca_h, pU_D_quadU, CoverParams.cb_h, pU_D_quadU]
  simp only [Dual.pow_eq, Dual.mul_eps, Dual.add_eps, Dual.mul_val, Dual.C_val, Dual.C_eps]
  simp only [E_fn, dE_da, dE_db, dE_dU, dE_dV, H_cub, dH_dS, dH_dQ, dH_dU, dH_dV,
    CoverParams.c0_V2, CoverParams.c0_V1, CoverParams.c0_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma dE2_along (a b U W a' b' W' : F) (hU : U ≠ 0) :
    W * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * W' * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * W * (dE_da 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * a' +
      dE_db 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * b' +
      dE_dU 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
      dE_dV 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * ((W' * U - W) / U ^ 2)) =
    (pU_D φ k5Params.q20 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) ^ 2 +
      pU_D φ k5Params.q11 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) +
      pU_D φ k5Params.q02 U * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) ^ 2 +
      (⟨W, W'⟩ : Dual F) * (Dual.C (φ k5Params.k2_V2) * (⟨W, W'⟩ : Dual F) ^ 2 +
        Dual.C (φ k5Params.k2_V1) * (⟨U, 1⟩ : Dual F) * (⟨W, W'⟩ : Dual F) +
        Dual.C (φ k5Params.k2_V0) * (⟨U, 1⟩ : Dual F) ^ 2)).eps := by
  rw [CoverParams.q20, pU_D_quadU, CoverParams.q11, pU_D_quadU, CoverParams.q02, pU_D_quadU]
  simp only [Dual.pow_eq, Dual.mul_eps, Dual.add_eps, Dual.mul_val, Dual.add_val, Dual.C_val, Dual.C_eps]
  simp only [E_fn, dE_da, dE_db, dE_dU, dE_dV, H_cub, dH_dS, dH_dQ, dH_dU, dH_dV,
    CoverParams.k2_V2, CoverParams.k2_V1, CoverParams.k2_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma dE3_along (a b U W a' b' W' : F) (hU : U ≠ 0) :
    W ^ 2 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    2 * U * W * W' * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * W ^ 2 * (dE_da 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * a' +
      dE_db 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * b' +
      dE_dU 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
      dE_dV 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * ((W' * U - W) / U ^ 2)) =
    (pU_D φ k5Params.c30 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) ^ 3 +
      pU_D φ k5Params.c21 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) ^ 2 * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) +
      pU_D φ k5Params.c12 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) ^ 2 +
      pU_D φ k5Params.c03 U * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) ^ 3 +
      (⟨W, W'⟩ : Dual F) ^ 2 * (Dual.C (φ k5Params.k3_V2) * (⟨W, W'⟩ : Dual F) ^ 2 +
        Dual.C (φ k5Params.k3_V1) * (⟨U, 1⟩ : Dual F) * (⟨W, W'⟩ : Dual F) +
        Dual.C (φ k5Params.k3_V0) * (⟨U, 1⟩ : Dual F) ^ 2)).eps := by
  rw [CoverParams.c30, pU_D_quadU, CoverParams.c21, pU_D_quadU, CoverParams.c12, pU_D_quadU,
    CoverParams.c03, pU_D_quadU]
  simp only [Dual.pow_eq, Dual.mul_eps, Dual.add_eps, Dual.mul_val, Dual.add_val, Dual.C_val, Dual.C_eps]
  simp only [E_fn, dE_da, dE_db, dE_dU, dE_dV, H_cub, dH_dS, dH_dQ, dH_dU, dH_dV,
    CoverParams.k3_V2, CoverParams.k3_V1, CoverParams.k3_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
    k5Params_inv3, map_zero, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

-- Homogenization identity relating `(M_abSQ ...).det` to `CoverParams.detM_W`.
private lemma detM_W_of_cover (U W : F) (hU : U ≠ 0) (hW0 : W ≠ 0)
    (hcb : pU φ k5Params.cb_h U ≠ 0) (hd1 : pUW φ k5Params.d1_z U W ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    let z := -pUW φ k5Params.d0_z U W / pUW φ k5Params.d1_z U W
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    let Cc := pUW φ k5Params.C_sub U W
    (M_abSQ (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)).det =
      -((W / U) / Cc ^ 2) ^ 4 * pUW φ k5Params.detM_W U W := by
  intro z a b Cc
  have pUW_add (x y : PairAlg K5[X]) : pUW φ (PairAlg.add x y) U W = pUW φ x U W + pUW φ y U W := by
    simp only [pUW, PairAlg.map_add, PairAlg.evalAt_add]
  have pUW_sub (x y : PairAlg K5[X]) : pUW φ (PairAlg.sub x y) U W = pUW φ x U W - pUW φ y U W := by
    simp only [pUW, PairAlg.map_sub, PairAlg.evalAt_sub]
  have pUW_smul (s : K5[X]) (x : PairAlg K5[X]) : pUW φ (PairAlg.smul s x) U W = pU φ s U * pUW φ x U W := by
    simp only [pUW, pU, PairAlg.map_smul, PairAlg.evalAt_smul, RingHom.comp_apply,
      Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]
  have pUW_pmul (x y : PairAlg K5[X]) : pUW φ (k5Params.pmul x y) U W = pUW φ x U W * pUW φ y U W := by
    simp only [pUW, CoverParams.pmul, PairAlg.map_mul, RingHom.comp_apply,
      Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]
    exact PairAlg.evalAt_mul (pU φ k5Params.bW U) (pU φ k5Params.cW U) W hW _ _
  have pUW_W : pUW φ PairAlg.W U W = W := by simp [pUW, PairAlg.map_W, PairAlg.evalAt_W]
  have pUW_zero : pUW φ PairAlg.zero U W = 0 := by simp [pUW, PairAlg.map_zero, PairAlg.evalAt_zero]
  have hCc_eq : Cc = W * pU φ k5Params.cb_h U * pUW φ k5Params.d1_z U W := by
    dsimp only [Cc, CoverParams.C_sub]; rw [pUW_pmul, pUW_W, pUW_smul]; ring
  have hCc_ne : Cc ≠ 0 := by rw [hCc_eq]; exact mul_ne_zero (mul_ne_zero hW0 hcb) hd1
  have hA_eq : pUW φ k5Params.A_sub U W = -pU φ k5Params.cb_h U * pUW φ k5Params.d0_z U W := by
    rw [CoverParams.A_sub, pUW_smul]; simp [pU]
  have hB_eq : pUW φ k5Params.B_sub U W =
      pU φ k5Params.ca_h U * pUW φ k5Params.d0_z U W - pUW φ k5Params.c0W U W * pUW φ k5Params.d1_z U W := by
    rw [CoverParams.B_sub, pUW_sub, pUW_smul, pUW_pmul]
  have ha_div : a = pUW φ k5Params.A_sub U W / Cc := by
    rw [hA_eq, hCc_eq]; dsimp only [a, z]; field_simp [hW0, hcb, hd1]
  have hb_div : b = pUW φ k5Params.B_sub U W / Cc := by
    rw [hB_eq, hCc_eq]; dsimp only [b, z]; field_simp [hW0, hcb, hd1]; ring
  let xS_p : PairAlg K5[X] := PairAlg.sub (PairAlg.smul (C k5Params.S) k5Params.C_sub)
    (PairAlg.smul (C k5Params.T) k5Params.A_sub)
  let xQ_p : PairAlg K5[X] := PairAlg.sub (PairAlg.smul (C k5Params.Q) k5Params.C_sub)
    (PairAlg.smul (C k5Params.T) k5Params.B_sub)
  have hξS_div : φ S_K - a * φ T_K = pUW φ xS_p U W / Cc := by
    dsimp only [xS_p]; rw [pUW_sub, pUW_smul, pUW_smul, ha_div]
    simp only [pU, Polynomial.map_C, eval_C, k5Params_S, k5Params_T]
    field_simp [hCc_ne]; ring
  have hξQ_div : φ Q_K - b * φ T_K = pUW φ xQ_p U W / Cc := by
    dsimp only [xQ_p]; rw [pUW_sub, pUW_smul, pUW_smul, hb_div]
    simp only [pU, Polynomial.map_C, eval_C, k5Params_Q, k5Params_T]
    field_simp [hCc_ne]; ring
  have hdHS_hom (s q : PairAlg K5[X]) :
      dH_dS (pUW φ s U W / Cc) (pUW φ q U W / Cc) U (W / U) =
        ((W / U) / Cc ^ 2) * pUW φ (k5Params.dH_dS_hom s q) U W := by
    simp only [CoverParams.dH_dS_hom, pUW_add, pUW_sub, pUW_smul, pUW_pmul, dH_dS, pU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv3,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_ofNat, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
      map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
    field_simp [hU, hCc_ne]; ring
  have hdHQ_hom (s q v0 : PairAlg K5[X]) :
      dH_dQ (pUW φ s U W / Cc) (pUW φ q U W / Cc) (pUW φ v0 U W / Cc) U (W / U) =
        ((W / U) / Cc ^ 2) * pUW φ (k5Params.dH_dQ_hom s q v0) U W := by
    simp only [CoverParams.dH_dQ_hom, pUW_add, pUW_sub, pUW_smul, pUW_pmul, dH_dQ, pU,
      CoverParams.inv9, CoverParams.inv27, k5Params_inv3, k5Params_inv7,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_ofNat, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
      map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
    field_simp [hU, hCc_ne]; ring
  set lam : F := (W / U) / Cc ^ 2
  have ha2_eq : q1_a2 a b U (W / U) = lam * pUW φ (k5Params.dH_dS_hom k5Params.A_sub k5Params.B_sub) U W := by
    rw [q1_a2, ha_div, hb_div, hdHS_hom]
  have ha0_eq : q1_a0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      lam * pUW φ (k5Params.dH_dS_hom xS_p xQ_p) U W := by
    rw [q1_a0, hξS_div, hξQ_div, hdHS_hom]
  have ha1_eq : q1_a1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      lam * (pUW φ (k5Params.dH_dS_hom (PairAlg.add k5Params.A_sub xS_p) (PairAlg.add k5Params.B_sub xQ_p)) U W -
        pUW φ (k5Params.dH_dS_hom k5Params.A_sub k5Params.B_sub) U W -
        pUW φ (k5Params.dH_dS_hom xS_p xQ_p) U W) := by
    rw [q1_a1, hξS_div, hξQ_div, ha_div, hb_div, ← add_div, ← add_div, ← pUW_add, ← pUW_add,
      hdHS_hom, hdHS_hom, hdHS_hom]; ring
  have hb2_eq : q2_b2 a b U (W / U) =
      lam * pUW φ (k5Params.dH_dQ_hom k5Params.A_sub k5Params.B_sub PairAlg.zero) U W := by
    rw [q2_b2, ha_div, hb_div, show (0 : F) = pUW φ PairAlg.zero U W / Cc by simp [pUW_zero], hdHQ_hom]
  have hb0_eq : q2_b0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      lam * pUW φ (k5Params.dH_dQ_hom xS_p xQ_p k5Params.C_sub) U W := by
    rw [q2_b0, hξS_div, hξQ_div, show (1 : F) = pUW φ k5Params.C_sub U W / Cc from (div_self hCc_ne).symm, hdHQ_hom]
  have hb1_eq : q2_b1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      lam * (pUW φ (k5Params.dH_dQ_hom (PairAlg.add k5Params.A_sub xS_p) (PairAlg.add k5Params.B_sub xQ_p) PairAlg.zero) U W -
        pUW φ (k5Params.dH_dQ_hom k5Params.A_sub k5Params.B_sub PairAlg.zero) U W -
        pUW φ (k5Params.dH_dQ_hom xS_p xQ_p PairAlg.zero) U W +
        pU φ (C (10 * k5Params.inv7) * X) U * pUW φ (k5Params.pmul k5Params.B_sub k5Params.C_sub) U W) := by
    rw [q2_b1, hξS_div, hξQ_div, ha_div, hb_div, ← add_div, ← add_div, ← pUW_add, ← pUW_add,
      show (0 : F) = pUW φ PairAlg.zero U W / Cc by simp [pUW_zero],
      hdHQ_hom, hdHQ_hom, hdHQ_hom, pUW_pmul]
    simp only [pU, k5Params_inv7, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
      eval_mul, eval_C, eval_X, eval_ofNat, map_mul, map_inv₀, map_ofNat]
    dsimp only [lam, Cc]
    field_simp [hU, hCc_ne]
  rw [M_abSQ_det]
  have hSmat : S_ab_mat a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      Matrix.of ![![0, 0, q1_a0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                         q2_b0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U)],
                  ![q1_a0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q2_b0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q1_a1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q2_b1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U)],
                  ![q1_a1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q2_b1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q1_a2 a b U (W / U), q2_b2 a b U (W / U)],
                  ![q1_a2 a b U (W / U), q2_b2 a b U (W / U), 0, 0]] := rfl
  rw [hSmat, S_ab_mat_det, ha2_eq, ha1_eq, ha0_eq, hb2_eq, hb1_eq, hb0_eq]
  have hdetM : pUW φ k5Params.detM_W U W =
      let a2 := pUW φ (k5Params.dH_dS_hom k5Params.A_sub k5Params.B_sub) U W
      let a0 := pUW φ (k5Params.dH_dS_hom xS_p xQ_p) U W
      let a1 := pUW φ (k5Params.dH_dS_hom (PairAlg.add k5Params.A_sub xS_p) (PairAlg.add k5Params.B_sub xQ_p)) U W - a2 - a0
      let b2 := pUW φ (k5Params.dH_dQ_hom k5Params.A_sub k5Params.B_sub PairAlg.zero) U W
      let b0 := pUW φ (k5Params.dH_dQ_hom xS_p xQ_p k5Params.C_sub) U W
      let b1 := pUW φ (k5Params.dH_dQ_hom (PairAlg.add k5Params.A_sub xS_p) (PairAlg.add k5Params.B_sub xQ_p) PairAlg.zero) U W -
        b2 - pUW φ (k5Params.dH_dQ_hom xS_p xQ_p PairAlg.zero) U W +
        pU φ (C (10 * k5Params.inv7) * X) U * pUW φ (k5Params.pmul k5Params.B_sub k5Params.C_sub) U W
      (a2 * b0 - a0 * b2) ^ 2 - (a2 * b1 - a1 * b2) * (a1 * b0 - a0 * b1) := by
    dsimp only [CoverParams.detM_W]
    simp only [pUW_sub, pUW_add, pUW_pmul, pUW_smul]
    ring
  rw [hdetM]; ring

end DualCoverDeriv


section BranchEvalBasic
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

end BranchEvalBasic

/-- **Main Pointwise Sheet Extraction & Residue Identity on `R_{34}`**:
At every `r ∈ R34`, there is a unique nondegenerate sheet `(a, b, r, V) ∈ CoverL^4`
solving `E_0 = E_1 = E_2 = E_3 = 0` with `J_fib.det ≠ 0` and `M_abSQ.det ≠ 0`, and the
simple-pole residue of `eta_L` at `r` equals `-P18_of ... / (81 * (J_fib ...).det)`. -/
theorem residue_eta_L_at_R34 (r : CoverL) (hr : r ∈ R34) :
    ∃ a b V : CoverL,
      (∀ k : Fin 4, E_fn k SL QL TL a b r V = 0) ∧
      r ≠ 0 ∧ V ≠ 0 ∧ r ≠ 1 ∧ V ≠ 1 ∧
      (J_fib SL QL TL a b r V).det ≠ 0 ∧
      (M_abSQ SL QL TL a b r V).det ≠ 0 ∧
      CrossedRationalResidue.residue r eta_L =
        -P18_of SL QL TL xL yL a b r V / (81 * (J_fib SL QL TL a b r V).det) := by
  have hrP34 : (P34_K5.map ιL_K5).eval r = 0 := mem_R34_iff.mp hr
  -- 1. All 11 coprimality nonvanishings at `r ∈ R34`.
  have hr0 : r ≠ 0 := by simpa using eval_ne_zero_of_isCoprime isCoprime_P34_X hrP34
  have hr1 : r ≠ 1 := by
    have h := eval_ne_zero_of_isCoprime isCoprime_P34_X_sub_1 hrP34
    simpa [sub_eq_zero] using h
  have hQ5 : pU ιL_K5 k5Params.Q5_z r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_P34_Q5 hrP34
  have hcb : pU ιL_K5 k5Params.cb_h r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_P34_cb_h hrP34
  have hnmWU : pU ιL_K5 k5Params.nm_WU r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_P34_nm_WU hrP34
  have hnmd1 : pU ιL_K5 (k5Params.pnm k5Params.d1_z) r ≠ 0 :=
    eval_ne_zero_of_isCoprime isCoprime_P34_nm_d1_z hrP34
  have hnmdiscE2 : pU ιL_K5 (k5Params.pnm k5Params.disc_E2z) r ≠ 0 :=
    eval_ne_zero_of_isCoprime isCoprime_P34_nm_disc_E2z hrP34
  have hnmdetM : pU ιL_K5 (k5Params.pnm k5Params.detM_W) r ≠ 0 :=
    eval_ne_zero_of_isCoprime isCoprime_P34_nm_detM_W hrP34
  have hP34d : (P34_K5.derivative.map ιL_K5).eval r ≠ 0 :=
    eval_ne_zero_of_isCoprime isCoprime_P34_P34_deriv hrP34
  have hcbm : (cb_h_m_K5.map ιL_K5).eval r ≠ 0 := by
    have h := congrArg (fun f : K5[X] => (f.map ιL_K5).eval r) cb_h_K5_eq_mul_monic
    simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C] at h
    have hcb' : (k5Params.cb_h.map ιL_K5).eval r ≠ 0 := hcb
    rw [h] at hcb'
    exact right_ne_zero_of_mul hcb'
  have hnmz0 : (k5Params.nm_z.map ιL_K5).eval r = 0 := by
    rw [nm_z_K5_factor]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_mul, eval_pow, eval_C, eval_X, hrP34, mul_zero]
  have hnmzd : (k5Params.nm_z.map ιL_K5).derivative.eval r ≠ 0 := by
    rw [nm_z_K5_factor]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      derivative_mul, eval_add, eval_mul, eval_pow, eval_C, eval_X, hrP34, mul_zero, zero_add,
      Polynomial.derivative_map]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((map_ne_zero_iff ιL_K5 ιL_K5.injective).mpr lc34_K5_ne_zero)
      (pow_ne_zero 15 hr0)) (pow_ne_zero 12 hcbm)) hP34d
  -- 2. Split fiber `E0` at `r` into distinct roots `w1 ≠ w2`, lift to `Dual CoverL`, select unique branch!
  obtain ⟨w1, w2, hw_sum, hw_prod, hw_sep⟩ := E0_splits_at_R34 r hr
  have h2w1 : 2 * w1 + pU ιL_K5 k5Params.bW r ≠ 0 := by
    have : 2 * w1 + pU ιL_K5 k5Params.bW r = w1 - w2 := by linear_combination hw_sum
    rw [this]; exact sub_ne_zero.mpr hw_sep
  have h2w2 : 2 * w2 + pU ιL_K5 k5Params.bW r ≠ 0 := by
    have : 2 * w2 + pU ιL_K5 k5Params.bW r = w2 - w1 := by linear_combination hw_sum
    rw [this]; exact sub_ne_zero.mpr hw_sep.symm
  set w1' : CoverL := -(pU_d ιL_K5 k5Params.bW r * w1 + pU_d ιL_K5 k5Params.cW r) /
    (2 * w1 + pU ιL_K5 k5Params.bW r)
  set w2' : CoverL := -(pU_d ιL_K5 k5Params.bW r * w2 + pU_d ιL_K5 k5Params.cW r) /
    (2 * w2 + pU ιL_K5 k5Params.bW r)
  have hW12_sum : (⟨w1, w1'⟩ : Dual CoverL) + ⟨w2, w2'⟩ = -pU_D ιL_K5 k5Params.bW r := by
    rw [pU_D_eq]
    ext
    · exact hw_sum
    · simp only [Dual.add_eps, Dual.neg_eps]
      have h1 : 2 * w1 + pU ιL_K5 k5Params.bW r = w1 - w2 := by linear_combination hw_sum
      have h2 : 2 * w2 + pU ιL_K5 k5Params.bW r = -(w1 - w2) := by linear_combination hw_sum
      dsimp only [w1', w2']; rw [h1, h2]
      have hne := sub_ne_zero.mpr hw_sep
      field_simp [hne]; ring
  have hW12_prod : (⟨w1, w1'⟩ : Dual CoverL) * ⟨w2, w2'⟩ = pU_D ιL_K5 k5Params.cW r := by
    rw [pU_D_eq]
    ext
    · exact hw_prod
    · simp only [Dual.mul_eps]
      have h1 : 2 * w1 + pU ιL_K5 k5Params.bW r = w1 - w2 := by linear_combination hw_sum
      have h2 : 2 * w2 + pU ιL_K5 k5Params.bW r = -(w1 - w2) := by linear_combination hw_sum
      dsimp only [w1', w2']; rw [h1, h2]
      have hne := sub_ne_zero.mpr hw_sep
      field_simp [hne]; ring
  have hres_nm_D : pUW_D ιL_K5 k5Params.res_z r w1 w1' * pUW_D ιL_K5 k5Params.res_z r w2 w2' =
      pU_D ιL_K5 k5Params.nm_z r := by
    let fD := Polynomial.eval₂RingHom (Dual.C.comp ιL_K5) (⟨r, 1⟩ : Dual CoverL)
    have hnm := PairAlg.evalAt_nm (fD k5Params.bW) (fD k5Params.cW)
      ⟨w1, w1'⟩ ⟨w2, w2'⟩ hW12_sum hW12_prod (PairAlg.map fD k5Params.res_z)
    rw [← PairAlg.map_nm] at hnm
    exact hnm.symm
  have hres_nm_val : pUW ιL_K5 k5Params.res_z r w1 * pUW ιL_K5 k5Params.res_z r w2 = 0 := by
    have h := congrArg Dual.val hres_nm_D
    simp only [Dual.mul_val, pUW_D_val, pU_D_eq] at h
    exact h.trans hnmz0
  have hres_nm_eps : pUW ιL_K5 k5Params.res_z r w1 * (pUW_D ιL_K5 k5Params.res_z r w2 w2').eps +
      (pUW_D ιL_K5 k5Params.res_z r w1 w1').eps * pUW ιL_K5 k5Params.res_z r w2 =
      (k5Params.nm_z.map ιL_K5).derivative.eval r := by
    have h := congrArg Dual.eps hres_nm_D
    simp only [Dual.mul_eps, pUW_D_val, pU_D_eq, pU_d] at h
    rw [Polynomial.derivative_map]
    exact h
  -- Select the unique branch `(w, w', w_c, w_c')` where `res_z(r, w) = 0`!
  have hbranch : ∃ w w' w_c w_c' : CoverL,
      (⟨w, w'⟩ : Dual CoverL) + ⟨w_c, w_c'⟩ = -pU_D ιL_K5 k5Params.bW r ∧
      (⟨w, w'⟩ : Dual CoverL) * ⟨w_c, w_c'⟩ = pU_D ιL_K5 k5Params.cW r ∧
      w ≠ w_c ∧
      pUW ιL_K5 k5Params.res_z r w = 0 ∧
      pUW ιL_K5 k5Params.res_z r w_c ≠ 0 ∧
      (pUW_D ιL_K5 k5Params.res_z r w w').eps * pUW ιL_K5 k5Params.res_z r w_c =
        (k5Params.nm_z.map ιL_K5).derivative.eval r := by
    rcases mul_eq_zero.mp hres_nm_val with h1 | h2
    · refine ⟨w1, w1', w2, w2', hW12_sum, hW12_prod, hw_sep, h1, ?_, ?_⟩
      · intro hc; rw [h1, hc, zero_mul, mul_zero, add_zero] at hres_nm_eps; exact hnmzd hres_nm_eps.symm
      · rw [h1, zero_mul, zero_add] at hres_nm_eps; exact hres_nm_eps
    · refine ⟨w2, w2', w1, w1', by rw [add_comm]; exact hW12_sum, by rw [mul_comm]; exact hW12_prod,
        hw_sep.symm, h2, ?_, ?_⟩
      · intro hc; rw [h2, hc, zero_mul, mul_zero, add_zero] at hres_nm_eps; exact hnmzd hres_nm_eps.symm
      · rw [h2, mul_zero, add_zero, mul_comm] at hres_nm_eps; exact hres_nm_eps
  obtain ⟨w, w', w_c, w_c', hW_sum_D, hW_prod_D, hw_sep_c, hres0, hresc, hres_eps_prod⟩ := hbranch
  have hWD : (⟨w, w'⟩ : Dual CoverL) ^ 2 + pU_D ιL_K5 k5Params.bW r * ⟨w, w'⟩ + pU_D ιL_K5 k5Params.cW r = 0 := by
    linear_combination (⟨w, w'⟩ : Dual CoverL) * hW_sum_D - hW_prod_D
  have hW_eq : w ^ 2 + pU ιL_K5 k5Params.bW r * w + pU ιL_K5 k5Params.cW r = 0 := by
    have h := congrArg Dual.val hWD
    simp only [Dual.pow_eq, Dual.add_val, Dual.mul_val, pU_D_eq, Dual.zero_val] at h
    exact h
  have hW_sum : w + w_c = -pU ιL_K5 k5Params.bW r := by
    have h := congrArg Dual.val hW_sum_D; simpa only [Dual.add_val, Dual.neg_val, pU_D_eq] using h
  have hW_prod : w * w_c = pU ιL_K5 k5Params.cW r := by
    have h := congrArg Dual.val hW_prod_D; simpa only [Dual.mul_val, pU_D_eq] using h
  -- Nonvanishings on the chosen branch `(r, w)`.
  have hnm_eval (x : PairAlg K5[X]) (h : pU ιL_K5 (k5Params.pnm x) r ≠ 0) : pUW ιL_K5 x r w ≠ 0 := by
    let fL := (Polynomial.evalRingHom r).comp (Polynomial.mapRingHom ιL_K5)
    have hfac := PairAlg.evalAt_nm (fL k5Params.bW) (fL k5Params.cW) w w_c hW_sum hW_prod (PairAlg.map fL x)
    rw [← PairAlg.map_nm] at hfac
    have h' : fL (PairAlg.nm k5Params.bW k5Params.cW x) ≠ 0 := h
    rw [hfac] at h'
    exact left_ne_zero_of_mul h'
  have hw_ne : w ≠ 0 := by
    have hcW_ne : pU ιL_K5 k5Params.cW r ≠ 0 := cW_eval_ne_zero hr0
    rw [← hW_prod] at hcW_ne
    exact left_ne_zero_of_mul hcW_ne
  have hV_ne : w / r ≠ 0 := div_ne_zero hw_ne hr0
  have hV1 : w / r ≠ 1 := by
    intro h1
    have hwr : w = r := (div_eq_one_iff_eq hr0).mp h1
    have h0 : pU ιL_K5 k5Params.nm_WU r = 0 := by
      simp only [pU, CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm, Polynomial.map_add,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
        Polynomial.map_X, Polynomial.map_one, eval_add, eval_sub, eval_mul, eval_pow,
        eval_neg, eval_X, eval_one]
      rw [hwr] at hW_eq; linear_combination hW_eq
    exact hnmWU h0
  have h2w_ne : 2 * w + pU ιL_K5 k5Params.bW r ≠ 0 := by
    have : 2 * w + pU ιL_K5 k5Params.bW r = w - w_c := by linear_combination hW_sum
    rw [this]; exact sub_ne_zero.mpr hw_sep_c
  have hd1_ne : pUW ιL_K5 k5Params.d1_z r w ≠ 0 := hnm_eval k5Params.d1_z hnmd1
  have hdiscE2_ne : pUW ιL_K5 k5Params.disc_E2z r w ≠ 0 := hnm_eval k5Params.disc_E2z hnmdiscE2
  have hdetM_ne : pUW ιL_K5 k5Params.detM_W r w ≠ 0 := hnm_eval k5Params.detM_W hnmdetM
  have hres_eps_ne : (pUW_D ιL_K5 k5Params.res_z r w w').eps ≠ 0 :=
    left_ne_zero_of_mul (hres_eps_prod.symm ▸ hnmzd)
  -- 3. Construct the sheet `(a_r, b_r, r, w / r)` and verify `E_0 = E_1 = E_2 = E_3 = 0`!
  set d2_2 := pUW ιL_K5 k5Params.d2_2 r w
  set d2_1 := pUW ιL_K5 k5Params.d2_1 r w
  set d2_0 := pUW ιL_K5 k5Params.d2_0 r w
  set d3_3 := pUW ιL_K5 k5Params.d3_3 r w
  set d3_2 := pUW ιL_K5 k5Params.d3_2 r w
  set d3_1 := pUW ιL_K5 k5Params.d3_1 r w
  set d3_0 := pUW ιL_K5 k5Params.d3_0 r w
  set d1_r := pUW ιL_K5 k5Params.d1_z r w
  set d0_r := pUW ιL_K5 k5Params.d0_z r w
  have hd2_2_eq : d2_2 = pU ιL_K5 k5Params.Q5_z r := by
    simp [d2_2, pUW, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, pU]
  have hd2_2_ne : d2_2 ≠ 0 := hd2_2_eq.symm ▸ hQ5
  have hd1_rem : d1_r = remDeg3_d1 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 := by
    have hmul := PairAlg.evalAt_mul (eval r (map ιL_K5 k5Params.bW)) (eval r (map ιL_K5 k5Params.cW)) w hW_eq
    simp only [d1_r, CoverParams.d1_z, remDeg3_d1, pUW, CoverParams.pmul, PairAlg.map_sub,
      PairAlg.map_mul, PairAlg.evalAt_sub, RingHom.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.coe_mapRingHom, hmul]
    rfl
  have hd0_rem : d0_r = remDeg3_d0 d2_2 d2_1 d2_0 d3_3 d3_2 d3_0 := by
    have hmul := PairAlg.evalAt_mul (eval r (map ιL_K5 k5Params.bW)) (eval r (map ιL_K5 k5Params.cW)) w hW_eq
    simp only [d0_r, CoverParams.d0_z, remDeg3_d0, pUW, CoverParams.pmul, PairAlg.map_sub,
      PairAlg.map_mul, PairAlg.evalAt_sub, RingHom.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.coe_mapRingHom, hmul]
    rfl
  have hres_syl5 : pUW ιL_K5 k5Params.res_z r w = syl5 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 d3_0 := by
    simp only [pUW, CoverParams.res_z, map_syl5Pair, RingHom.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.coe_mapRingHom]
    exact evalAt_syl5Pair _ _ _ _ _ _ _ _ _ w hW_eq
  set z_r : CoverL := -d0_r / d1_r
  have hE2_zr : d2_2 * z_r ^ 2 + d2_1 * z_r + d2_0 = 0 := by
    have hqs := q2_sq_mul_syl5 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 d3_0
    rw [← hres_syl5, hres0, mul_zero] at hqs
    dsimp only at hqs
    change 0 = d2_2 * (remDeg3_d0 d2_2 d2_1 d2_0 d3_3 d3_2 d3_0) ^ 2 -
      remDeg3_d0 d2_2 d2_1 d2_0 d3_3 d3_2 d3_0 * remDeg3_d1 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 * d2_1 +
      remDeg3_d1 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 ^ 2 * d2_0 at hqs
    rw [← hd1_rem, ← hd0_rem] at hqs
    apply mul_left_cancel₀ (pow_ne_zero 2 hd1_ne)
    dsimp only [z_r]; field_simp [hd1_ne]; linear_combination -hqs
  have hE3_zr : d3_3 * z_r ^ 3 + d3_2 * z_r ^ 2 + d3_1 * z_r + d3_0 = 0 := by
    have hrem := remDeg3_eq d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 d3_0 z_r
    rw [hE2_zr, ← hd1_rem, ← hd0_rem, mul_zero, zero_add] at hrem
    have hlin : d1_r * z_r + d0_r = 0 := by dsimp only [z_r]; field_simp [hd1_ne]; ring
    rw [hlin] at hrem
    exact (mul_eq_zero.mp hrem).resolve_left (pow_ne_zero 2 hd2_2_ne)
  set a_r : CoverL := z_r / w
  set b_r : CoverL := -(pU ιL_K5 k5Params.ca_h r * z_r + pUW ιL_K5 k5Params.c0W r w) /
    (w * pU ιL_K5 k5Params.cb_h r)
  set V_r : CoverL := w / r
  have hE_all : ∀ k : Fin 4, E_fn k SL QL TL a_r b_r r V_r = 0 := by
    intro k; fin_cases k
    · have h0 := E0_of_cover ιL_K5 r w hr0
      rw [hW_eq, mul_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left hr0
    · have h1 := E1_of_cover ιL_K5 a_r b_r r w hr0 hW_eq
      have hrhs : pU ιL_K5 k5Params.ca_h r * (w * a_r) + pU ιL_K5 k5Params.cb_h r * (w * b_r) +
          pUW ιL_K5 k5Params.c0W r w = 0 := by
        dsimp only [a_r, b_r]; field_simp [hw_ne, hcb]; ring
      rw [hrhs] at h1
      exact (mul_eq_zero.mp h1).resolve_left hr0
    · have h2 := E2_z_of_cover ιL_K5 z_r r w hr0 hw_ne hcb hW_eq
      dsimp only at h2
      change r * w * pU ιL_K5 k5Params.cb_h r ^ 2 * E_fn 2 SL QL TL a_r b_r r V_r =
        d2_2 * z_r ^ 2 + d2_1 * z_r + d2_0 at h2
      rw [hE2_zr] at h2
      exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero (mul_ne_zero hr0 hw_ne) (pow_ne_zero 2 hcb))
    · have h3 := E3_z_of_cover ιL_K5 z_r r w hr0 hw_ne hcb hW_eq
      dsimp only at h3
      change r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E_fn 3 SL QL TL a_r b_r r V_r =
        d3_3 * z_r ^ 3 + d3_2 * z_r ^ 2 + d3_1 * z_r + d3_0 at h3
      rw [hE3_zr] at h3
      exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero (mul_ne_zero hr0 (pow_ne_zero 2 hw_ne)) (pow_ne_zero 3 hcb))
  -- 4. Compute `(M_abSQ ...).det ≠ 0` directly from `detM_W_of_cover`!
  have hM_ne : (M_abSQ SL QL TL a_r b_r r V_r).det ≠ 0 := by
    have hdet := detM_W_of_cover ιL_K5 r w hr0 hw_ne hcb hd1_ne hW_eq
    dsimp only at hdet
    rw [hdet]
    have hCc_ne : pUW ιL_K5 k5Params.C_sub r w ≠ 0 := by
      have hCc : pUW ιL_K5 k5Params.C_sub r w = w * pU ιL_K5 k5Params.cb_h r * d1_r := by
        simp only [pUW, CoverParams.C_sub, CoverParams.pmul, PairAlg.map_mul, PairAlg.map_smul,
          PairAlg.map_W, RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]
        rw [PairAlg.evalAt_mul (pU ιL_K5 k5Params.bW r) (pU ιL_K5 k5Params.cW r) w hW_eq,
          PairAlg.evalAt_W, PairAlg.evalAt_smul]
        change w * (pU ιL_K5 k5Params.cb_h r * d1_r) = _
        ring
      rw [hCc]; exact mul_ne_zero (mul_ne_zero hw_ne hcb) hd1_ne
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 4 (div_ne_zero hV_ne (pow_ne_zero 2 hCc_ne)))) hdetM_ne
  -- 5. Compute `(J_fib SL QL TL a_r b_r r V_r).det` via `Dual CoverL` + `HodgeComputer.Formal.QuadraticCovers.det_J_fib_schur` + `syl5_eq_prod_roots`!
  set D22 := pUW_D ιL_K5 k5Params.d2_2 r w w'
  set D21 := pUW_D ιL_K5 k5Params.d2_1 r w w'
  set D20 := pUW_D ιL_K5 k5Params.d2_0 r w w'
  set D33 := pUW_D ιL_K5 k5Params.d3_3 r w w'
  set D32 := pUW_D ιL_K5 k5Params.d3_2 r w w'
  set D31 := pUW_D ιL_K5 k5Params.d3_1 r w w'
  set D30 := pUW_D ιL_K5 k5Params.d3_0 r w w'
  have h2dz_ne : 2 * d2_2 * z_r + d2_1 ≠ 0 := by
    have hsq : (2 * d2_2 * z_r + d2_1) ^ 2 = pUW ιL_K5 k5Params.disc_E2z r w := by
      have hdisc : pUW ιL_K5 k5Params.disc_E2z r w = d2_1 ^ 2 - 4 * d2_2 * d2_0 := by
        simp only [pUW, CoverParams.disc_E2z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_smul,
          PairAlg.map_mul, PairAlg.evalAt_sub, PairAlg.evalAt_smul, RingHom.comp_apply,
          Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom, Polynomial.map_ofNat, eval_ofNat]
        simp only [PairAlg.evalAt_mul _ _ w hW_eq]; ring
      rw [hdisc]; linear_combination 4 * d2_2 * hE2_zr
    intro h0; rw [h0, zero_pow (by omega)] at hsq; exact hdiscE2_ne hsq.symm
  set z_r' : CoverL := -(D22.eps * z_r ^ 2 + D21.eps * z_r + D20.eps) / (2 * d2_2 * z_r + d2_1)
  set Z_D : Dual CoverL := ⟨z_r, z_r'⟩
  have hD2_Z : D22 * Z_D ^ 2 + D21 * Z_D + D20 = 0 := by
    ext
    · simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq, Dual.zero_val, D22, D21, D20, pUW_D_val]
      exact hE2_zr
    · simp only [Dual.add_eps, Dual.mul_eps, Dual.pow_eq, Dual.zero_eps, D22, D21, D20, pUW_D_val,
        Z_D, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      change d2_2 * (2 * z_r * z_r') + D22.eps * z_r ^ 2 + (d2_1 * z_r' + D21.eps * z_r) + D20.eps = 0
      have hz' : (2 * d2_2 * z_r + d2_1) * z_r' = -(D22.eps * z_r ^ 2 + D21.eps * z_r + D20.eps) :=
        mul_div_cancel₀ _ h2dz_ne
      linear_combination hz'
  set W_D : Dual CoverL := ⟨w, w'⟩
  set cb_D : Dual CoverL := pU_D ιL_K5 k5Params.cb_h r
  set ca_D : Dual CoverL := pU_D ιL_K5 k5Params.ca_h r
  set c0W_D : Dual CoverL := pUW_D ιL_K5 k5Params.c0W r w w'
  have hW_D_val : W_D.val ≠ 0 := hw_ne
  have hcb_D_val : cb_D.val ≠ 0 := by simpa [cb_D, pU_D_eq] using hcb
  set A_D : Dual CoverL := Z_D * Dual.invOfNe W_D hW_D_val
  set B_D : Dual CoverL := -(ca_D * Z_D + c0W_D) * Dual.invOfNe (W_D * cb_D) (mul_ne_zero hW_D_val hcb_D_val)
  have hA_val : A_D.val = a_r := by simp [A_D, Z_D, W_D, Dual.invOfNe, a_r, div_eq_mul_inv]
  have hB_val : B_D.val = b_r := by
    simp [B_D, Z_D, W_D, Dual.invOfNe, b_r, ca_D, cb_D, c0W_D, pU_D_eq, pUW_D_val, div_eq_mul_inv]; ring
  set a_r' : CoverL := A_D.eps
  set b_r' : CoverL := B_D.eps
  have hA_eq : (⟨a_r, a_r'⟩ : Dual CoverL) = A_D := by ext <;> simp [hA_val, a_r']
  have hB_eq : (⟨b_r, b_r'⟩ : Dual CoverL) = B_D := by ext <;> simp [hB_val, b_r']
  have hWA_D : W_D * A_D = Z_D := by
    dsimp only [A_D]; rw [mul_comm Z_D, ← mul_assoc, Dual.mul_invOfNe, one_mul]
  have hcbWB_D : cb_D * (W_D * B_D) = -(ca_D * Z_D + c0W_D) := by
    dsimp only [B_D]
    calc cb_D * (W_D * (-(ca_D * Z_D + c0W_D) * Dual.invOfNe (W_D * cb_D) (mul_ne_zero hW_D_val hcb_D_val)))
        = -(ca_D * Z_D + c0W_D) * ((W_D * cb_D) * Dual.invOfNe (W_D * cb_D) (mul_ne_zero hW_D_val hcb_D_val)) := by ring
      _ = -(ca_D * Z_D + c0W_D) := by rw [Dual.mul_invOfNe, mul_one]
  set V_r' : CoverL := (w' * r - w) / r ^ 2
  set M : Matrix (Fin 4) (Fin 4) CoverL := J_fib SL QL TL a_r b_r r V_r
  have hM00 : M 0 0 = 0 := rfl
  have hM01 : M 0 1 = 0 := rfl
  have hM0 : M 0 2 + M 0 3 * V_r' = 0 := by
    have h0 := dE0_along ιL_K5 a_r b_r r w w' hr0
    rw [hE_all 0, zero_add, hWD, mul_zero, Dual.zero_eps] at h0
    exact (mul_eq_zero.mp h0).resolve_left hr0
  have hM1 : M 1 0 * a_r' + M 1 1 * b_r' + M 1 2 + M 1 3 * V_r' = 0 := by
    have h1 := dE1_along ιL_K5 a_r b_r r w a_r' b_r' w' hr0
    rw [hE_all 1, zero_add, hA_eq, hB_eq] at h1
    have hc0 := pUW_D_toUW ιL_K5 k5Params.c0_V0 k5Params.c0_V1 k5Params.c0_V2 r w w' hWD
    have hrhs_D : ca_D * (W_D * A_D) + cb_D * (W_D * B_D) +
        (Dual.C (ιL_K5 k5Params.c0_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.c0_V1) * ⟨r, 1⟩ * W_D +
          Dual.C (ιL_K5 k5Params.c0_V0) * ⟨r, 1⟩ ^ 2) = 0 := by
      rw [← hc0]
      change ca_D * (W_D * A_D) + cb_D * (W_D * B_D) + c0W_D = 0
      rw [hWA_D, hcbWB_D]; ring
    have h1_rhs : (ca_D * (W_D * A_D) + cb_D * (W_D * B_D) +
        Dual.C (ιL_K5 k5Params.c0_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.c0_V1) * ⟨r, 1⟩ * W_D +
        Dual.C (ιL_K5 k5Params.c0_V0) * ⟨r, 1⟩ ^ 2) = 0 := by linear_combination hrhs_D
    rw [h1_rhs, Dual.zero_eps] at h1
    exact (mul_eq_zero.mp h1).resolve_left hr0
  have hM2 : M 2 0 * a_r' + M 2 1 * b_r' + M 2 2 + M 2 3 * V_r' = 0 := by
    have h2 := dE2_along ιL_K5 a_r b_r r w a_r' b_r' w' hr0
    rw [hE_all 2, mul_zero, mul_zero, zero_add, zero_add, hA_eq, hB_eq] at h2
    have hk2 : pUW_D ιL_K5 k5Params.k2W r w w' =
        Dual.C (ιL_K5 k5Params.k2_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k2_V1) * ⟨r, 1⟩ * W_D +
          Dual.C (ιL_K5 k5Params.k2_V0) * ⟨r, 1⟩ ^ 2 :=
      pUW_D_toUW ιL_K5 k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2 r w w' hWD
    have h2D : pU_D ιL_K5 2 r = 2 := pU_D_ofNat ιL_K5 2 r
    have hD22_eq : D22 = pU_D ιL_K5 k5Params.q20 r * cb_D ^ 2 -
        pU_D ιL_K5 k5Params.q11 r * ca_D * cb_D + pU_D ιL_K5 k5Params.q02 r * ca_D ^ 2 := by
      simp only [D22, CoverParams.d2_2, CoverParams.Q5_z, pUW_D_ofScalar,
        pU_D_add, pU_D_sub, pU_D_mul, pU_D_pow]; rfl
    have hD21_eq : D21 = (-pU_D ιL_K5 k5Params.q11 r * cb_D + 2 * pU_D ιL_K5 k5Params.q02 r * ca_D) * c0W_D := by
      simp only [D21, CoverParams.d2_1, pUW_D_smul, pU_D_add, pU_D_mul, pU_D_neg, h2D]; rfl
    have hD20_eq : D20 = pU_D ιL_K5 k5Params.q02 r * c0W_D ^ 2 +
        cb_D ^ 2 * (W_D * pUW_D ιL_K5 k5Params.k2W r w w') := by
      simp only [D20, CoverParams.d2_0, pUW_D_add, pUW_D_smul, pUW_D_pmul ιL_K5 _ _ r w w' hWD,
        pUW_D_W, pU_D_pow]
      change pU_D ιL_K5 k5Params.q02 r * (c0W_D * c0W_D) +
        cb_D ^ 2 * (W_D * pUW_D ιL_K5 k5Params.k2W r w w') = _
      ring
    have hcb2_rhs : cb_D ^ 2 *
        (pU_D ιL_K5 k5Params.q20 r * (W_D * A_D) ^ 2 +
          pU_D ιL_K5 k5Params.q11 r * (W_D * A_D) * (W_D * B_D) +
          pU_D ιL_K5 k5Params.q02 r * (W_D * B_D) ^ 2 +
          W_D * (Dual.C (ιL_K5 k5Params.k2_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k2_V1) * ⟨r, 1⟩ * W_D +
            Dual.C (ιL_K5 k5Params.k2_V0) * ⟨r, 1⟩ ^ 2)) = 0 := by
      rw [← hk2, hWA_D]
      have hcomb : cb_D ^ 2 * (pU_D ιL_K5 k5Params.q20 r * Z_D ^ 2 +
          pU_D ιL_K5 k5Params.q11 r * Z_D * (W_D * B_D) +
          pU_D ιL_K5 k5Params.q02 r * (W_D * B_D) ^ 2 +
          W_D * pUW_D ιL_K5 k5Params.k2W r w w') = D22 * Z_D ^ 2 + D21 * Z_D + D20 := by
        rw [hD22_eq, hD21_eq, hD20_eq]
        linear_combination (pU_D ιL_K5 k5Params.q11 r * Z_D * cb_D +
          pU_D ιL_K5 k5Params.q02 r * (cb_D * (W_D * B_D) - (ca_D * Z_D + c0W_D))) * hcbWB_D
      rw [hcomb, hD2_Z]
    let hcb2_inv := Dual.invOfNe (cb_D ^ 2) (by simp only [Dual.pow_eq]; exact pow_ne_zero 2 hcb_D_val)
    have hrhs0 : pU_D ιL_K5 k5Params.q20 r * (W_D * A_D) ^ 2 +
        pU_D ιL_K5 k5Params.q11 r * (W_D * A_D) * (W_D * B_D) +
        pU_D ιL_K5 k5Params.q02 r * (W_D * B_D) ^ 2 +
        W_D * (Dual.C (ιL_K5 k5Params.k2_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k2_V1) * ⟨r, 1⟩ * W_D +
          Dual.C (ιL_K5 k5Params.k2_V0) * ⟨r, 1⟩ ^ 2) = 0 := by
      have hmul := congrArg (hcb2_inv * ·) hcb2_rhs
      rw [← mul_assoc, Dual.invOfNe_mul, one_mul, mul_zero] at hmul
      exact hmul
    rw [hrhs0, Dual.zero_eps] at h2
    exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hr0 hw_ne)
  set E3_dot : CoverL := M 3 0 * a_r' + M 3 1 * b_r' + M 3 2 + M 3 3 * V_r'
  have hE3_D_eps : (D33 * Z_D ^ 3 + D32 * Z_D ^ 2 + D31 * Z_D + D30).eps =
      r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E3_dot := by
    have h3 := dE3_along ιL_K5 a_r b_r r w a_r' b_r' w' hr0
    rw [hE_all 3, mul_zero, mul_zero, zero_add, zero_add, hA_eq, hB_eq] at h3
    have hk3 : pUW_D ιL_K5 k5Params.k3W r w w' =
        Dual.C (ιL_K5 k5Params.k3_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k3_V1) * ⟨r, 1⟩ * W_D +
          Dual.C (ιL_K5 k5Params.k3_V0) * ⟨r, 1⟩ ^ 2 :=
      pUW_D_toUW ιL_K5 k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2 r w w' hWD
    have h2D : pU_D ιL_K5 2 r = 2 := pU_D_ofNat ιL_K5 2 r
    have h3D : pU_D ιL_K5 3 r = 3 := pU_D_ofNat ιL_K5 3 r
    have hD33_eq : D33 = pU_D ιL_K5 k5Params.c30 r * cb_D ^ 3 -
        pU_D ιL_K5 k5Params.c21 r * ca_D * cb_D ^ 2 +
        pU_D ιL_K5 k5Params.c12 r * ca_D ^ 2 * cb_D -
        pU_D ιL_K5 k5Params.c03 r * ca_D ^ 3 := by
      simp only [D33, CoverParams.d3_3, CoverParams.Q7_z, pUW_D_ofScalar,
        pU_D_add, pU_D_sub, pU_D_mul, pU_D_pow]; rfl
    have hD32_eq : D32 = (-pU_D ιL_K5 k5Params.c21 r * cb_D ^ 2 +
        2 * pU_D ιL_K5 k5Params.c12 r * ca_D * cb_D -
        3 * pU_D ιL_K5 k5Params.c03 r * ca_D ^ 2) * c0W_D := by
      simp only [D32, CoverParams.d3_2, pUW_D_smul, pU_D_add, pU_D_sub, pU_D_mul, pU_D_neg,
        pU_D_pow, h2D, h3D]; rfl
    have hD31_eq : D31 = (pU_D ιL_K5 k5Params.c12 r * cb_D - 3 * pU_D ιL_K5 k5Params.c03 r * ca_D) * c0W_D ^ 2 := by
      simp only [D31, CoverParams.d3_1, pUW_D_smul, pUW_D_pmul ιL_K5 _ _ r w w' hWD,
        pU_D_sub, pU_D_mul, h3D]
      change (pU_D ιL_K5 k5Params.c12 r * cb_D - 3 * pU_D ιL_K5 k5Params.c03 r * ca_D) * (c0W_D * c0W_D) = _
      ring
    have hD30_eq : D30 = -pU_D ιL_K5 k5Params.c03 r * c0W_D ^ 3 +
        cb_D ^ 3 * (W_D ^ 2 * pUW_D ιL_K5 k5Params.k3W r w w') := by
      simp only [D30, CoverParams.d3_0, pUW_D_add, pUW_D_smul, pUW_D_pmul ιL_K5 _ _ r w w' hWD,
        pUW_D_W, pU_D_neg, pU_D_pow]
      change -pU_D ιL_K5 k5Params.c03 r * (c0W_D * (c0W_D * c0W_D)) +
        cb_D ^ 3 * (W_D * W_D * pUW_D ιL_K5 k5Params.k3W r w w') = _
      ring
    set R3_D : Dual CoverL := pU_D ιL_K5 k5Params.c30 r * (W_D * A_D) ^ 3 +
      pU_D ιL_K5 k5Params.c21 r * (W_D * A_D) ^ 2 * (W_D * B_D) +
      pU_D ιL_K5 k5Params.c12 r * (W_D * A_D) * (W_D * B_D) ^ 2 +
      pU_D ιL_K5 k5Params.c03 r * (W_D * B_D) ^ 3 +
      W_D ^ 2 * (Dual.C (ιL_K5 k5Params.k3_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k3_V1) * ⟨r, 1⟩ * W_D +
        Dual.C (ιL_K5 k5Params.k3_V0) * ⟨r, 1⟩ ^ 2)
    have hD3_eq : D33 * Z_D ^ 3 + D32 * Z_D ^ 2 + D31 * Z_D + D30 = cb_D ^ 3 * R3_D := by
      dsimp only [R3_D]
      rw [← hk3, hWA_D, hD33_eq, hD32_eq, hD31_eq, hD30_eq]
      set Y := cb_D * (W_D * B_D)
      set Z := -(ca_D * Z_D + c0W_D)
      have hstep : cb_D ^ 3 * (pU_D ιL_K5 k5Params.c30 r * Z_D ^ 3 +
          pU_D ιL_K5 k5Params.c21 r * Z_D ^ 2 * (W_D * B_D) +
          pU_D ιL_K5 k5Params.c12 r * Z_D * (W_D * B_D) ^ 2 +
          pU_D ιL_K5 k5Params.c03 r * (W_D * B_D) ^ 3 +
          W_D ^ 2 * pUW_D ιL_K5 k5Params.k3W r w w') =
          pU_D ιL_K5 k5Params.c30 r * cb_D ^ 3 * Z_D ^ 3 +
          pU_D ιL_K5 k5Params.c21 r * cb_D ^ 2 * Z_D ^ 2 * Y +
          pU_D ιL_K5 k5Params.c12 r * cb_D * Z_D * Y ^ 2 +
          pU_D ιL_K5 k5Params.c03 r * Y ^ 3 +
          cb_D ^ 3 * (W_D ^ 2 * pUW_D ιL_K5 k5Params.k3W r w w') := by dsimp only [Y]; ring
      rw [hstep, show Y = Z from hcbWB_D]; dsimp only [Z]; ring
    have hR3_val : R3_D.val = 0 := by
      have hval := congrArg Dual.val hD3_eq
      simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq, D33, D32, D31, D30, pUW_D_val,
        cb_D, pU_D_eq] at hval
      change d3_3 * z_r ^ 3 + d3_2 * z_r ^ 2 + d3_1 * z_r + d3_0 = pU ιL_K5 k5Params.cb_h r ^ 3 * R3_D.val at hval
      rw [hE3_zr] at hval
      exact (mul_eq_zero.mp hval.symm).resolve_left (pow_ne_zero 3 hcb)
    have heps := congrArg Dual.eps hD3_eq
    rw [Dual.mul_eps, hR3_val, mul_zero, add_zero] at heps
    have hcb3_val : (cb_D ^ 3).val = pU ιL_K5 k5Params.cb_h r ^ 3 := by
      simp [cb_D, Dual.pow_eq, pU_D_eq]
    rw [heps, hcb3_val, ← h3]
    dsimp only [E3_dot, M, J_fib]; ring
  -- Relate `(pUW_D res_z).eps` to `E3_dot` via `syl5_eq_prod_roots` in `Dual CoverL`!
  have hres_eps_eq : (pUW_D ιL_K5 k5Params.res_z r w w').eps =
      -d1_r * (2 * d2_2 * z_r + d2_1) * r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E3_dot := by
    have hD22_val : D22.val ≠ 0 := by simpa [D22, pUW_D_val] using hd2_2_ne
    set Z2_D : Dual CoverL := -D21 * Dual.invOfNe D22 hD22_val - Z_D
    have hD21_fac : D21 = -D22 * (Z_D + Z2_D) := by
      dsimp only [Z2_D]
      calc D21 = (D22 * Dual.invOfNe D22 hD22_val) * D21 := by rw [Dual.mul_invOfNe, one_mul]
        _ = -D22 * (Z_D + (-D21 * Dual.invOfNe D22 hD22_val - Z_D)) := by ring
    have hD20_fac : D20 = D22 * Z_D * Z2_D := by
      linear_combination hD2_Z - Z_D * (by rw [hD21_fac]; ring : D22 * (Z_D + Z2_D) + D21 = 0)
    have hres_D_eq : pUW_D ιL_K5 k5Params.res_z r w w' =
        D22 ^ 3 * (D33 * Z_D ^ 3 + D32 * Z_D ^ 2 + D31 * Z_D + D30) *
          (D33 * Z2_D ^ 3 + D32 * Z2_D ^ 2 + D31 * Z2_D + D30) := by
      have hs : pUW_D ιL_K5 k5Params.res_z r w w' = syl5 D22 D21 D20 D33 D32 D31 D30 := by
        let fD := Polynomial.eval₂RingHom (Dual.C.comp ιL_K5) (⟨r, 1⟩ : Dual CoverL)
        change PairAlg.evalAt (⟨w, w'⟩ : Dual CoverL) (PairAlg.map fD k5Params.res_z) = _
        rw [CoverParams.res_z, map_syl5Pair]
        exact evalAt_syl5Pair (fD k5Params.bW) (fD k5Params.cW)
          (PairAlg.map fD k5Params.d2_2) (PairAlg.map fD k5Params.d2_1) (PairAlg.map fD k5Params.d2_0)
          (PairAlg.map fD k5Params.d3_3) (PairAlg.map fD k5Params.d3_2) (PairAlg.map fD k5Params.d3_1)
          (PairAlg.map fD k5Params.d3_0) (⟨w, w'⟩ : Dual CoverL) hWD
      rw [hs, hD21_fac, hD20_fac]
      exact syl5_eq_prod_roots D22 D33 D32 D31 D30 Z_D Z2_D
    have hE3_Z_val : (D33 * Z_D ^ 3 + D32 * Z_D ^ 2 + D31 * Z_D + D30).val = 0 := by
      simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq, D33, D32, D31, D30, pUW_D_val]
      exact hE3_zr
    have hz2_val : Z2_D.val = -d2_1 / d2_2 - z_r := by
      simp only [Z2_D, Z_D, Dual.sub_val, Dual.mul_val, Dual.neg_val, Dual.invOfNe, D21, D22, pUW_D_val]
      change -d2_1 * d2_2⁻¹ - z_r = -d2_1 / d2_2 - z_r
      ring
    have hE3_Z2_val : d2_2 ^ 3 * (D33 * Z2_D ^ 3 + D32 * Z2_D ^ 2 + D31 * Z2_D + D30).val =
        -d1_r * (2 * d2_2 * z_r + d2_1) := by
      have hv : (D33 * Z2_D ^ 3 + D32 * Z2_D ^ 2 + D31 * Z2_D + D30).val =
          d3_3 * Z2_D.val ^ 3 + d3_2 * Z2_D.val ^ 2 + d3_1 * Z2_D.val + d3_0 := by
        simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq, D33, D32, D31, D30, pUW_D_val]; rfl
      rw [hv]
      have hqZ2 : d2_2 * Z2_D.val ^ 2 + d2_1 * Z2_D.val + d2_0 = 0 := by
        rw [hz2_val]; field_simp [hd2_2_ne]; linear_combination d2_2 * hE2_zr
      have hrem := remDeg3_eq d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 d3_0 Z2_D.val
      rw [hqZ2, mul_zero, zero_add, ← hd1_rem, ← hd0_rem] at hrem
      have hd0_eq : d0_r = -d1_r * z_r := by dsimp only [z_r]; field_simp [hd1_ne]
      calc d2_2 ^ 3 * (d3_3 * Z2_D.val ^ 3 + d3_2 * Z2_D.val ^ 2 + d3_1 * Z2_D.val + d3_0)
          = d2_2 * (d2_2 ^ 2 * (d3_3 * Z2_D.val ^ 3 + d3_2 * Z2_D.val ^ 2 + d3_1 * Z2_D.val + d3_0)) := by ring
        _ = d2_2 * (d1_r * Z2_D.val + d0_r) := by rw [hrem]
        _ = -d1_r * (2 * d2_2 * z_r + d2_1) := by rw [hz2_val, hd0_eq]; field_simp [hd2_2_ne]; ring
    have heps := congrArg Dual.eps hres_D_eq
    rw [Dual.mul_eps, Dual.mul_eps, Dual.mul_val, hE3_Z_val, mul_zero, mul_zero, add_zero, zero_mul, zero_add] at heps
    have hD22_3_val : (D22 ^ 3).val = d2_2 ^ 3 := by simp [D22, Dual.pow_eq, pUW_D_val]; rfl
    rw [hD22_3_val, hE3_D_eps] at heps
    calc (pUW_D ιL_K5 k5Params.res_z r w w').eps
        = (d2_2 ^ 3 * (D33 * Z2_D ^ 3 + D32 * Z2_D ^ 2 + D31 * Z2_D + D30).val) *
            (r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E3_dot) := by linear_combination heps
      _ = -d1_r * (2 * d2_2 * z_r + d2_1) * r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E3_dot := by
          rw [hE3_Z2_val]; ring
  have hM_det : M.det = -ιL_K5 k5Params.Av0 * (2 * w + pU ιL_K5 k5Params.bW r) *
      (pUW_D ιL_K5 k5Params.res_z r w w').eps / (d1_r * r ^ 3 * w * pU ιL_K5 k5Params.cb_h r ^ 4) := by
    have hschur := HodgeComputer.Formal.QuadraticCovers.det_J_fib_schur M a_r' b_r' V_r' E3_dot hM00 hM01 hM0 hM1 hM2 rfl
    have h03 : M 0 3 = ιL_K5 k5Params.Av0 * (2 * w + pU ιL_K5 k5Params.bW r) := J_fib_03 ιL_K5 a_r b_r r w hr0
    have hmin : M 1 1 * M 2 0 - M 1 0 * M 2 1 =
        w * (2 * d2_2 * z_r + d2_1) / (r ^ 2 * pU ιL_K5 k5Params.cb_h r) :=
      J_fib_minor12 ιL_K5 z_r r w hr0 hw_ne hcb
    rw [hschur, h03, hmin, hres_eps_eq]
    field_simp [hd1_ne, hr0, hw_ne, hcb]
  have hAv0_ne : ιL_K5 k5Params.Av0 ≠ 0 := (map_ne_zero_iff ιL_K5 ιL_K5.injective).mpr Av0_K5_ne_zero
  have hJ_ne : M.det ≠ 0 := by
    rw [hM_det]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hAv0_ne) h2w_ne) hres_eps_ne)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hd1_ne (pow_ne_zero 3 hr0)) hw_ne) (pow_ne_zero 4 hcb))
  -- 6. Compute `CrossedRationalResidue.residue r eta_L` via `residue_div_simpleZero` + `ValAC`!
  refine ⟨a_r, b_r, V_r, hE_all, hr0, hV_ne, hr1, hV1, hJ_ne, hM_ne, ?_⟩
  let g_P18 : CoverL → CoverL := fun z =>
    SheetCalculus.P18_of SL QL TL xL yL
      (z / w) (-(pU ιL_K5 k5Params.ca_h r * z + pUW ιL_K5 k5Params.c0W r w) / (w * pU ιL_K5 k5Params.cb_h r))
      r V_r
  obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ :=
    valAC_interp4 hW_eq (fun hz => valAC_P18_z_AC hr0 hr1 hw_ne hcb hnmWU hW_eq hz)
  obtain ⟨hP1_val, hP0_val⟩ :=
    valAC_remDeg4 hW_eq (valAC_pairC r w _) (valAC_pairC r w _) (valAC_pairC r w _) hp4 hp3 hp2 hp1 hp0
  set q := interp4 g_P18
  set P1_r := remDeg4_P1 d2_2 d2_1 d2_0 q.1 q.2.1 q.2.2.1 q.2.2.2.1
  set P0_r := remDeg4_P0 d2_2 d2_1 d2_0 q.1 q.2.1 q.2.2.1 q.2.2.2.2
  have hnum_raw_val : ValAC r w eta_AC_num
      (-(P1_r * d0_r - P0_r * d1_r) * r ^ 3 * w * pU ιL_K5 k5Params.cb_h r ^ 4) := by
    have hmul {x y : A_C} {vx vy : CoverL} := @valAC_mul r w hW_eq x y vx vy
    have hpow {x : A_C} {vx : CoverL} := @valAC_pow r w hW_eq x vx
    exact hmul (hmul (hmul (valAC_neg (valAC_sub
      (hmul hP1_val (valAC_pairC r w _)) (hmul hP0_val (valAC_pairC r w _))))
      (hpow (valAC_U_C r w) 3)) (valAC_W_C r w)) (hpow (valAC_polyC r w _) 4)
  have h81_ne : (81 : CoverL) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  set D_poly : K5[X] := C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3
  have hD_eval : (D_poly.map ιL_K5).eval r = 81 * ιL_K5 k5Params.Av0 * pU ιL_K5 k5Params.Q5_z r ^ 3 := by
    simp only [D_poly, pU, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_ofNat, eval_mul, eval_pow, eval_C, eval_ofNat, map_mul, map_ofNat]
  have hD_ne : (D_poly.map ιL_K5).eval r ≠ 0 := by
    rw [hD_eval]; exact mul_ne_zero (mul_ne_zero h81_ne hAv0_ne) (pow_ne_zero 3 hQ5)
  set num_r : A_C := eta_AC_num / polyC D_poly
  have hnum_val : ValAC r w num_r
      ((-(P1_r * d0_r - P0_r * d1_r) * r ^ 3 * w * pU ιL_K5 k5Params.cb_h r ^ 4) /
        (81 * ιL_K5 k5Params.Av0 * pU ιL_K5 k5Params.Q5_z r ^ 3)) := by
    rw [← hD_eval]
    exact valAC_div_of_reg hW_eq hnum_raw_val (valAC_polyC r w D_poly)
      (regAC_div_polyC hnum_raw_val.reg hD_ne) hD_ne
  -- Compute `-(P1_r * d0_r - P0_r * d1_r)` using `remDeg4_eq` and `P18_of_isPolyDeg4`!
  have hP18_deg4 : IsPolyDeg 4 g_P18 := by
    have h := P18_of_isPolyDeg4 (SL (L := CoverL)) QL TL xL yL r V_r
      (1 / w) 0 (-pU ιL_K5 k5Params.ca_h r / (w * pU ιL_K5 k5Params.cb_h r))
      (-pUW ιL_K5 k5Params.c0W r w / (w * pU ιL_K5 k5Params.cb_h r))
    refine h.congr (fun z => ?_)
    dsimp only [g_P18]
    congr 1
    · ring
    · field_simp [hw_ne, hcb]; ring
  have hq_zr : q.1 * z_r ^ 4 + q.2.1 * z_r ^ 3 + q.2.2.1 * z_r ^ 2 + q.2.2.2.1 * z_r + q.2.2.2.2 =
      P18_of SL QL TL xL yL a_r b_r r V_r := (hP18_deg4.eq_deg4 z_r).symm
  have hcomb_zr : -(P1_r * d0_r - P0_r * d1_r) =
      d1_r * pU ιL_K5 k5Params.Q5_z r ^ 3 * P18_of SL QL TL xL yL a_r b_r r V_r := by
    have hrem := remDeg4_eq d2_2 d2_1 d2_0 q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 z_r
    rw [hE2_zr, mul_zero, zero_add, hq_zr] at hrem
    change d2_2 ^ 3 * P18_of SL QL TL xL yL a_r b_r r V_r = P1_r * z_r + P0_r at hrem
    have hd0_eq : d0_r = -d1_r * z_r := by dsimp only [z_r]; field_simp [hd1_ne]
    rw [← hd2_2_eq, hd0_eq]
    linear_combination -d1_r * hrem
  -- Express `eta_L` via `trace_AC_euler` and apply `residue_div_simpleZero`!
  have heta_euler : eta = ((coordsAC num_r).c1 * toRat k5Params.res_z.c0 -
      (coordsAC num_r).c0 * toRat k5Params.res_z.c1) / toRat k5Params.nm_z := by
    have heta_eq : eta_AC = num_r / (pairC k5Params.res_z * (2 * W_C + polyC k5Params.bW)) := by
      dsimp only [num_r, D_poly]
      rw [eta_AC, polyC_81_Av0_Q5_eq, div_div]
      exact congrArg (eta_AC_num / ·) (by ring)
    have hnm_rat : PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) (PairAlg.map toRat k5Params.res_z) ≠ 0 := by
      rw [← PairAlg.map_nm, show PairAlg.nm k5Params.bW k5Params.cW k5Params.res_z = k5Params.nm_z from rfl]
      exact polynomialMap_ne_zero nm_z_K5_ne_zero
    conv_lhs =>
      rw [eta, heta_eq, ← evalAC_coordsAC num_r, pairC, polyC,
        trace_AC_euler (coordsAC num_r) (PairAlg.map toRat k5Params.res_z) hnm_rat, ← PairAlg.map_nm]
    rfl
  set N_L : RatFunc CoverL := mapRatFunc ιL_K5
    ((coordsAC num_r).c1 * toRat k5Params.res_z.c0 - (coordsAC num_r).c0 * toRat k5Params.res_z.c1)
  have hN_reg : RegularAt r N_L := by
    simp only [N_L, map_sub, map_mul, mapRatFunc_algebraMap]
    exact regAt_sub_local (regAt_mul_local hnum_val.reg.c1 (RegularAt.polynomial r _))
      (regAt_mul_local hnum_val.reg.c0 (RegularAt.polynomial r _))
  have heta_L_eq : eta_L = N_L / algebraMap CoverL[X] (RatFunc CoverL) (k5Params.nm_z.map ιL_K5) := by
    rw [eta_L, heta_euler, map_div₀, mapRatFunc_algebraMap]
  rw [heta_L_eq, residue_div_simpleZero r N_L (k5Params.nm_z.map ιL_K5) hN_reg hnmz0 hnmzd]
  have hval_N : valueAt r N_L = pUW ιL_K5 k5Params.res_z r w_c * valAC r w num_r /
      (2 * w + pU ιL_K5 k5Params.bW r) := by
    simp only [N_L, map_sub, map_mul, mapRatFunc_algebraMap]
    rw [valueAt_mul_of_regularAt hnum_val.reg.c1 (RegularAt.polynomial r _),
        valueAt_mul_of_regularAt hnum_val.reg.c0 (RegularAt.polynomial r _),
        valueAt_polynomial, valueAt_polynomial]
    have hc0_eq : (k5Params.res_z.c0.map ιL_K5).eval r = -(k5Params.res_z.c1.map ιL_K5).eval r * w := by
      have h := hres0; simp only [pUW_eq, pU] at h; linear_combination h
    have hrc_eq : pUW ιL_K5 k5Params.res_z r w_c =
        -(k5Params.res_z.c1.map ιL_K5).eval r * (2 * w + pU ιL_K5 k5Params.bW r) := by
      simp only [pUW_eq, pU, hc0_eq]
      linear_combination (k5Params.res_z.c1.map ιL_K5).eval r * hW_sum
    dsimp only [valAC]
    rw [hc0_eq, hrc_eq, eq_div_iff h2w_ne]
    ring
  rw [hval_N, hnum_val.eq, hcomb_zr, ← hres_eps_prod, hM_det]
  field_simp [h81_ne, hAv0_ne, hQ5, h2w_ne, hresc, hres_eps_ne, hd1_ne, hr0, hw_ne, hcb]

private lemma resDivW_L_sum {ι : Type*} (s : Finset ι) (f : ι → Fin 4 → CoverL) :
    resDivW_L (fun i => ∑ a ∈ s, f a i) = ∑ a ∈ s, resDivW_L (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, resDivW_L, map_zero, zero_mul, zero_div, sub_self, Finset.sum_const_zero]
  | insert a s ha ih =>
    have hfun : (fun i => ∑ b ∈ insert a s, f b i) = fun i => f a i + ∑ b ∈ s, f b i := by
      funext i; exact Finset.sum_insert ha
    rw [hfun, resDivW_L_add, ih, Finset.sum_insert ha]

/-- **Summed Horizontal Sheet Theorem on `CoverL`**:
There exists a single 4-component vector `w_H_L : Fin 4 → CoverL` (the sum of `w_horiz` over
all 34 nondegenerate sheets above `R34`) whose weighted residue divergence equals the sum of
all 34 finite residues of `eta_L` on `R34`. -/
theorem sum_R34_eq_sheet_div :
    ∃ w_H_L : Fin 4 → CoverL,
      2 * ιL (L := CoverL) W2_K * ιL (L := CoverL) H0_K ^ 2 * resDivW_L w_H_L =
        ∑ r ∈ R34, CrossedRationalResidue.residue r eta_L := by
  classical
  have hex : ∀ r : {r // r ∈ R34}, ∃ a b V : CoverL,
      (∀ k : Fin 4, E_fn k SL QL TL a b r.1 V = 0) ∧
      r.1 ≠ 0 ∧ V ≠ 0 ∧ r.1 ≠ 1 ∧ V ≠ 1 ∧
      (J_fib SL QL TL a b r.1 V).det ≠ 0 ∧
      (M_abSQ SL QL TL a b r.1 V).det ≠ 0 ∧
      CrossedRationalResidue.residue r.1 eta_L =
        -P18_of SL QL TL xL yL a b r.1 V / (81 * (J_fib SL QL TL a b r.1 V).det) :=
    fun r => residue_eta_L_at_R34 r.1 r.2
  choose a b V hspec using hex
  refine ⟨fun i => ∑ r ∈ R34.attach, w_horiz (a r) (b r) r.1 (V r) i, ?_⟩
  rw [resDivW_L_sum, Finset.mul_sum, ← Finset.sum_attach R34]
  apply Finset.sum_congr rfl
  intro r _
  obtain ⟨hE, hr0, hV0, hr1, hV1, hJ, hM, hres⟩ := hspec r
  rw [HodgeComputer.SymmetricSexticResidual.Proof.sheet_horiz_identity (a r) (b r) r.1 (V r) hE hr0 hV0 hr1 hV1 hJ hM, ← hres]

end SplittingAndResidues

end SymmetricSexticResidual.CoverResidue

open scoped BigOperators in
theorem solution :
    ∃ w_H_L : Fin 4 → SymmetricSexticResidual.CoverResidue.CoverL,
      2 * SymmetricSexticResidual.SheetCalculus.ιL (L := SymmetricSexticResidual.CoverResidue.CoverL)
          SymmetricSexticResidual.K5Field.W2_K *
        SymmetricSexticResidual.SheetCalculus.ιL (L := SymmetricSexticResidual.CoverResidue.CoverL)
          SymmetricSexticResidual.K5Field.H0_K ^ 2 *
        SymmetricSexticResidual.SheetCalculus.resDivW_L w_H_L =
        ∑ r ∈ SymmetricSexticResidual.CoverResidue.R34,
          CrossedRationalResidue.residue r SymmetricSexticResidual.CoverResidue.eta_L :=
  SymmetricSexticResidual.CoverResidue.sum_R34_eq_sheet_div
