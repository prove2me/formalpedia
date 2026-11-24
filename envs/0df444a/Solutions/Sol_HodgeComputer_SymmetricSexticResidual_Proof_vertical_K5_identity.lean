-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.vertical_K5_identity
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:44:58.08911+00:00
-- url     : https://prove2.me/submissions/56cf24f5-1f0a-4735-82b4-4788c350acd3

import Definitions.Def_HodgeComputerFormal_PolyEncoding
import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_VerticalData
import Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_biv_denote_eq_of_kronecker3

set_option autoImplicit false

noncomputable section
namespace SymmetricSexticResidual.VerticalIdentity
open SymmetricSexticResidual SymmetricSexticResidual.K5Field
open PolynomialEncoding.KroneckerCheck SymmetricSexticResidual.VerticalData
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open MvPolynomial
open scoped BigOperators

def eAdd : Expr → Expr → Expr
  | .num 0, b => b
  | a, .num 0 => a
  | a, b => .add a b

def eSub : Expr → Expr → Expr
  | a, .num 0 => a
  | .num 0, b => .neg b
  | a, b => .sub a b

def eMul : Expr → Expr → Expr
  | .num 0, _ => .num 0
  | _, .num 0 => .num 0
  | .num 1, b => b
  | a, .num 1 => a
  | a, b => .mul a b

def exprDeriv (i : ℕ) : Expr → Expr
  | .num _ | .natCast _ | .intCast _ => .num 0
  | .var j => if j = i then .num 1 else .num 0
  | .neg a => match exprDeriv i a with | .num 0 => .num 0 | da => .neg da
  | .add a b => eAdd (exprDeriv i a) (exprDeriv i b)
  | .sub a b => eSub (exprDeriv i a) (exprDeriv i b)
  | .mul a b => eAdd (eMul (exprDeriv i a) b) (eMul a (exprDeriv i b))
  | .pow a k =>
    match k with
    | 0 => .num 0
    | 1 => exprDeriv i a
    | k' + 1 =>
      match exprDeriv i a with
      | .num 0 => .num 0
      | da =>
        let p := if k' = 1 then a else .pow a k'
        eMul (eMul (.num (k' + 1 : ℤ)) p) da


lemma evalExpr3_eAdd (a b : Expr) : evalExpr3 (eAdd a b) = evalExpr3 a + evalExpr3 b := by
  unfold eAdd; split <;> simp [evalExpr3, ringEval]

lemma evalExpr3_eSub (a b : Expr) : evalExpr3 (eSub a b) = evalExpr3 a - evalExpr3 b := by
  unfold eSub; split <;> simp [evalExpr3, ringEval]

lemma evalExpr3_eMul (a b : Expr) : evalExpr3 (eMul a b) = evalExpr3 a * evalExpr3 b := by
  unfold eMul; split <;> simp [evalExpr3, ringEval]

lemma pderiv_evalExpr3_012 (k : ℕ) (hk : k < 3) :
    ∀ e : Expr, pderiv (⟨k, by omega⟩ : Fin 5) (evalExpr3 e) = evalExpr3 (exprDeriv k e)
  | .num c => by simp [evalExpr3, ringEval, exprDeriv]
  | .natCast c => by simp [evalExpr3, ringEval, exprDeriv]
  | .intCast c => by simp [evalExpr3, ringEval, exprDeriv]
  | .var j => by
    dsimp only [evalExpr3, ringEval, exprDeriv]
    match j with
    | 0 =>
      change pderiv (⟨k, by omega⟩ : Fin 5) (X 0) = _
      rw [pderiv_X]
      by_cases h0 : (0 : ℕ) = k
      · subst h0; simp [Pi.single_eq_same, ringEval]
      · have hne : (0 : Fin 5) ≠ ⟨k, by omega⟩ := fun h => h0 (congrArg Fin.val h)
        simp [Pi.single_eq_of_ne hne, h0, ringEval]
    | 1 =>
      change pderiv (⟨k, by omega⟩ : Fin 5) (X 1) = _
      rw [pderiv_X]
      by_cases h1 : (1 : ℕ) = k
      · subst h1; simp [Pi.single_eq_same, ringEval]
      · have hne : (1 : Fin 5) ≠ ⟨k, by omega⟩ := fun h => h1 (congrArg Fin.val h)
        simp [Pi.single_eq_of_ne hne, h1, ringEval]
    | 2 =>
      change pderiv (⟨k, by omega⟩ : Fin 5) (X 2) = _
      rw [pderiv_X]
      by_cases h2 : (2 : ℕ) = k
      · subst h2; simp [Pi.single_eq_same, ringEval]
      · have hne : (2 : Fin 5) ≠ ⟨k, by omega⟩ := fun h => h2 (congrArg Fin.val h)
        simp [Pi.single_eq_of_ne hne, h2, ringEval]
    | j' + 3 =>
      have hne : j' + 3 ≠ k := fun h => by
        have hle : 3 ≤ k := h ▸ Nat.le_add_left 3 j'
        omega
      change pderiv (⟨k, by omega⟩ : Fin 5) 0 = _
      simp [hne, ringEval]
  | .neg a => by
    have ih := pderiv_evalExpr3_012 k hk a
    dsimp only [evalExpr3, ringEval, exprDeriv] at ih ⊢
    rw [map_neg, ih]
    split
    · rename_i h0; rw [h0]; simp [ringEval]
    · rfl
  | .add a b => by
    rw [show evalExpr3 (.add a b) = evalExpr3 a + evalExpr3 b from rfl, map_add,
      pderiv_evalExpr3_012 k hk a, pderiv_evalExpr3_012 k hk b, exprDeriv, evalExpr3_eAdd]
  | .sub a b => by
    rw [show evalExpr3 (.sub a b) = evalExpr3 a - evalExpr3 b from rfl, map_sub,
      pderiv_evalExpr3_012 k hk a, pderiv_evalExpr3_012 k hk b, exprDeriv, evalExpr3_eSub]
  | .mul a b => by
    rw [show evalExpr3 (.mul a b) = evalExpr3 a * evalExpr3 b from rfl, Derivation.leibniz,
      pderiv_evalExpr3_012 k hk a, pderiv_evalExpr3_012 k hk b, exprDeriv, evalExpr3_eAdd,
      evalExpr3_eMul, evalExpr3_eMul, smul_eq_mul, smul_eq_mul]
    ring
  | .pow a m => by
    rw [show evalExpr3 (.pow a m) = evalExpr3 a ^ m from rfl, Derivation.leibniz_pow,
      pderiv_evalExpr3_012 k hk a, smul_eq_mul, nsmul_eq_mul]
    match m with
    | 0 => simp [exprDeriv, evalExpr3, ringEval]
    | 1 => simp [exprDeriv]
    | m'' + 2 =>
      change ((m'' + 2 : ℕ) : Poly5) * (evalExpr3 a ^ (m'' + 1) * evalExpr3 (exprDeriv k a)) =
        evalExpr3 (match exprDeriv k a with
          | .num 0 => .num 0
          | da => eMul (eMul (.num ((m'' + 1 : ℕ) + 1 : ℤ))
              (if m'' + 1 = 1 then a else .pow a (m'' + 1))) da)
      split
      · rename_i h0; rw [h0]; simp [evalExpr3, ringEval]
      · rw [evalExpr3_eMul, evalExpr3_eMul]
        have hc : evalExpr3 (.num ((m'' + 1 : ℕ) + 1 : ℤ)) = ((m'' + 2 : ℕ) : Poly5) := by
          simp [evalExpr3, ringEval]; ring
        rw [hc]
        by_cases hm : m'' + 1 = 1
        · simp [hm, evalExpr3]; ring
        · have hm0 : m'' ≠ 0 := by omega
          simp [hm0, evalExpr3, ringEval]; ring

lemma pderiv_evalExpr3_34 (i : Fin 5) (hi : 3 ≤ i.val) : ∀ e : Expr, pderiv i (evalExpr3 e) = 0
  | .num _ => by simp [evalExpr3, ringEval]
  | .natCast _ => by simp [evalExpr3, ringEval]
  | .intCast _ => by simp [evalExpr3, ringEval]
  | .var j => by
    dsimp only [evalExpr3, ringEval]
    match j with
    | 0 =>
      change pderiv i (X 0) = 0; rw [pderiv_X]
      have hne : (0 : Fin 5) ≠ i := fun h => by have := congrArg Fin.val h; simp at this; omega
      exact Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) hne 1
    | 1 =>
      change pderiv i (X 1) = 0; rw [pderiv_X]
      have hne : (1 : Fin 5) ≠ i := fun h => by have := congrArg Fin.val h; simp at this; omega
      exact Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) hne 1
    | 2 =>
      change pderiv i (X 2) = 0; rw [pderiv_X]
      have hne : (2 : Fin 5) ≠ i := fun h => by have := congrArg Fin.val h; simp at this; omega
      exact Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) hne 1
    | _ + 3 => change pderiv i 0 = 0; simp
  | .neg a => by
    rw [show evalExpr3 (.neg a) = -evalExpr3 a from rfl, map_neg, pderiv_evalExpr3_34 i hi a, neg_zero]
  | .add a b => by
    rw [show evalExpr3 (.add a b) = evalExpr3 a + evalExpr3 b from rfl, map_add,
      pderiv_evalExpr3_34 i hi a, pderiv_evalExpr3_34 i hi b, add_zero]
  | .sub a b => by
    rw [show evalExpr3 (.sub a b) = evalExpr3 a - evalExpr3 b from rfl, map_sub,
      pderiv_evalExpr3_34 i hi a, pderiv_evalExpr3_34 i hi b, sub_zero]
  | .mul a b => by
    rw [show evalExpr3 (.mul a b) = evalExpr3 a * evalExpr3 b from rfl, Derivation.leibniz,
      pderiv_evalExpr3_34 i hi a, pderiv_evalExpr3_34 i hi b]; simp
  | .pow a m => by
    rw [show evalExpr3 (.pow a m) = evalExpr3 a ^ m from rfl, Derivation.leibniz_pow,
      pderiv_evalExpr3_34 i hi a]; simp

-- Biv operations and derivatives in all 5 variables
def bivDeriv (k : ℕ) : Biv → Biv
  | .nil => .nil
  | .cons a i j p =>
    match k with
    | 0 | 1 | 2 =>
      match exprDeriv k a with
      | .num 0 => bivDeriv k p
      | da => .cons da i j (bivDeriv k p)
    | 3 => dx (.cons a i j p)
    | _ => dy (.cons a i j p)


lemma evalBiv5_bivAdd (p q : Biv) : evalBiv5 (bivAdd p q) = evalBiv5 p + evalBiv5 q :=
  merge_denote vSQT (X 3) (X 4) 512 p q

lemma evalBiv5_bivSub (p q : Biv) : evalBiv5 (bivSub p q) = evalBiv5 p - evalBiv5 q := by
  rw [bivSub, evalBiv5, merge_denote, negBiv_denote, ← sub_eq_add_neg]; rfl

lemma evalBiv5_bivMul (p q : Biv) : evalBiv5 (bivMul p q) = evalBiv5 p * evalBiv5 q :=
  multiply_denote vSQT (X 3) (X 4) p q

lemma evalBiv5_bivScale (c : ℤ) (p : Biv) : evalBiv5 (bivScale c p) = C (c : ℂ) * evalBiv5 p := by
  rw [bivScale, evalBiv5, scale_denote]
  simp [ringEval, evalBiv5]

lemma pderiv_evalBiv5_012 (k : ℕ) (hk : k < 3) (p : Biv) :
    pderiv (⟨k, by omega⟩ : Fin 5) (evalBiv5 p) = evalBiv5 (bivDeriv k p) := by
  induction p with
  | nil => simp [evalBiv5, bivDeriv, denote]
  | cons a i j p ih =>
    rw [evalBiv5, denote, map_add]
    have hX3 : pderiv (⟨k, by omega⟩ : Fin 5) (X 3 : Poly5) = 0 := by
      have hne : (3 : Fin 5) ≠ ⟨k, by omega⟩ := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      rw [pderiv_X]; exact Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) hne 1
    have hX4 : pderiv (⟨k, by omega⟩ : Fin 5) (X 4 : Poly5) = 0 := by
      have hne : (4 : Fin 5) ≠ ⟨k, by omega⟩ := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      rw [pderiv_X]; exact Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) hne 1
    have hterm : pderiv (⟨k, by omega⟩ : Fin 5) (ringEval vSQT a * X 3 ^ i * X 4 ^ j) =
        evalExpr3 (exprDeriv k a) * X 3 ^ i * X 4 ^ j := by
      simp only [Derivation.leibniz, Derivation.leibniz_pow, hX3, hX4, smul_eq_mul, nsmul_eq_mul,
        mul_zero, zero_add]
      have ha : pderiv (⟨k, by omega⟩ : Fin 5) (ringEval vSQT a) = evalExpr3 (exprDeriv k a) :=
        pderiv_evalExpr3_012 k hk a
      rw [ha]; ring
    rw [hterm, show denote vSQT (X 3) (X 4) p = evalBiv5 p from rfl, ih]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> (
      change _ = evalBiv5 (match exprDeriv _ a with
        | .num 0 => bivDeriv _ p | da => .cons da i j (bivDeriv _ p))
      split
      · rename_i h0; rw [h0]; simp [evalExpr3, ringEval]
      · simp [evalBiv5, denote, evalExpr3])

lemma pderiv_evalBiv5_3 (p : Biv) : pderiv (3 : Fin 5) (evalBiv5 p) = evalBiv5 (dx p) := by
  induction p with
  | nil => simp [evalBiv5, dx, denote]
  | cons a i j p ih =>
    rw [evalBiv5, denote, map_add]
    have ha0 : pderiv (3 : Fin 5) (ringEval vSQT a) = 0 := pderiv_evalExpr3_34 3 (by decide) a
    have hX3 : pderiv (3 : Fin 5) (X 3 : Poly5) = 1 := by simp [pderiv_X]
    have hX4 : pderiv (3 : Fin 5) (X 4 : Poly5) = 0 := by
      rw [pderiv_X]; exact Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) (by decide : (4 : Fin 5) ≠ 3) 1
    rw [show denote vSQT (X 3) (X 4) p = evalBiv5 p from rfl, ih]
    cases i with
    | zero =>
      simp only [dx, pow_zero, mul_one, Derivation.leibniz, Derivation.leibniz_pow, ha0, hX4,
        smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, zero_add]
    | succ i =>
      simp only [dx, evalBiv5, denote, ringEval, Derivation.leibniz, Derivation.leibniz_pow,
        ha0, hX3, hX4, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero,
        mul_one, Nat.add_sub_cancel]
      ring

lemma pderiv_evalBiv5_4 (p : Biv) : pderiv (4 : Fin 5) (evalBiv5 p) = evalBiv5 (dy p) := by
  induction p with
  | nil => simp [evalBiv5, dy, denote]
  | cons a i j p ih =>
    rw [evalBiv5, denote, map_add]
    have ha0 : pderiv (4 : Fin 5) (ringEval vSQT a) = 0 := pderiv_evalExpr3_34 4 (by decide) a
    have hX3 : pderiv (4 : Fin 5) (X 3 : Poly5) = 0 := by
      rw [pderiv_X]; exact Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) (by decide : (3 : Fin 5) ≠ 4) 1
    have hX4 : pderiv (4 : Fin 5) (X 4 : Poly5) = 1 := by simp [pderiv_X]
    rw [show denote vSQT (X 3) (X 4) p = evalBiv5 p from rfl, ih]
    cases j with
    | zero =>
      simp only [dy, pow_zero, mul_one, Derivation.leibniz, Derivation.leibniz_pow, ha0, hX3,
        smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, zero_add]
    | succ j =>
      simp only [dy, evalBiv5, denote, ringEval, Derivation.leibniz, Derivation.leibniz_pow,
        ha0, hX3, hX4, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero,
        mul_one, Nat.add_sub_cancel]
      ring

lemma pderiv_evalBiv5 (i : Fin 5) (p : Biv) : pderiv i (evalBiv5 p) = evalBiv5 (bivDeriv i.val p) := by
  fin_cases i
  · exact pderiv_evalBiv5_012 0 (by decide) p
  · exact pderiv_evalBiv5_012 1 (by decide) p
  · exact pderiv_evalBiv5_012 2 (by decide) p
  · change pderiv 3 (evalBiv5 p) = evalBiv5 (bivDeriv 3 p)
    rw [pderiv_evalBiv5_3]; cases p <;> rfl
  · change pderiv 4 (evalBiv5 p) = evalBiv5 (bivDeriv 4 p)
    rw [pderiv_evalBiv5_4]; cases p <;> rfl


def eRad_biv (p : Biv) : Biv :=
  bivAdd (scale (.num 1) 1 0 (dx p)) (scale (.num 1) 0 1 (dy p))

def NA_Q_biv : Biv :=
  bivSub (bivMul (bivScale 2 W2_biv) (eRad_biv MA_biv)) (bivMul MA_biv (eRad_biv W2_biv))

def pois_biv (u D : Biv) (a b : ℕ) (Fe : Biv) (negSign : Bool) : Biv :=
  let Fa := bivDeriv a Fe; let Fb := bivDeriv b Fe
  let Wa := bivDeriv a W2_biv; let Wb := bivDeriv b W2_biv
  let Da := bivDeriv a D; let Db := bivDeriv b D
  let ua := bivDeriv a u; let ub := bivDeriv b u
  let t1 := bivMul (bivMul (bivScale 2 W2_biv) D) (bivSub (bivMul Fa ub) (bivMul Fb ua))
  let t2 := bivMul (bivMul u D) (bivSub (bivMul Fa Wb) (bivMul Fb Wa))
  let t3 := bivMul (bivMul (bivScale 2 W2_biv) u) (bivSub (bivMul Fa Db) (bivMul Fb Da))
  let t := bivSub (bivSub t1 t2) t3
  if negSign then negBiv t else t

def dV_int_biv : Biv :=
  bivAdd (bivAdd (bivAdd (pois_biv u0_biv H0_int_biv 4 0 F5_int_biv true)
                         (pois_biv u1_biv H0_int_biv 4 1 F5_int_biv true))
                 (bivAdd (pois_biv u2_biv H0_int_biv 4 2 F5_int_biv true)
                         (pois_biv u3_biv H0_int_biv 3 0 F5_int_biv false)))
         (bivAdd (bivAdd (pois_biv u4_biv H0_int_biv 3 1 F5_int_biv false)
                         (pois_biv u5_biv H0_int_biv 3 2 F5_int_biv false))
                 (pois_biv u6_biv (.cons (.num 1) 0 0 .nil) 4 3 F5_xy_biv false))

def vertLHS_biv : Biv :=
  bivSub (bivSub (bivMul (bivScale D_u6 NA_Q_biv) H0_int_biv) (bivScale 7 dV_int_biv))
    (bivScale 12 P_horiz_biv)

def vertRHS_biv : Biv :=
  bivMul (bivScale 4 Q_vert_biv) F5_int_biv

-- Bridge lemmas for base Bivs
lemma evalBiv5_H0_int : evalBiv5 H0_int_biv = 7 * H0_5 := by
  simp only [H0_int_biv, H0_int_e, eS, eQ, eT, evalBiv5, denote, ringEval, vSQT,
    H0_5, H0_4, H0_3, poly4ToPoly5, poly3ToPoly4, tanIdx, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, eval₂Hom_X', eval₂Hom_C, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  have h5 : (7 : Poly5) * C (5 / 7 : ℂ) = 5 := by
    rw [show (7 : Poly5) = C 7 from rfl, ← map_mul]
    have : (7 : ℂ) * (5 / 7 : ℂ) = 5 := by norm_num
    rw [this]; rfl
  have h10 : (7 : Poly5) * C (10 / 7 : ℂ) = 10 := by
    rw [show (7 : Poly5) = C 7 from rfl, ← map_mul]
    have : (7 : ℂ) * (10 / 7 : ℂ) = 10 := by norm_num
    rw [this]; rfl
  linear_combination -(X 1 ^ 2) * h5 - X 1 * h10

lemma evalBiv5_F5_int : evalBiv5 F5_int_biv = 7 * F5 := by
  have h0 : evalBiv5 H0_int_biv = evalExpr3 H0_int_e := by simp [H0_int_biv, evalBiv5, denote, evalExpr3]
  rw [F5_int_biv, evalBiv5, denote, denote, denote, denote]
  change 21 * X 0 * X 3 ^ 2 * 1 + (21 * X 2 * 1 * X 4 ^ 2 + (evalExpr3 H0_int_e * 1 * 1 + 0)) = 7 * F5
  rw [← h0, evalBiv5_H0_int, F5]; ring

lemma evalBiv5_F5_xy : evalBiv5 F5_xy_biv = 3 * X 0 * X 3 ^ 2 + 3 * X 2 * X 4 ^ 2 := by
  simp [F5_xy_biv, eS, eT, evalBiv5, denote, ringEval, vSQT]

lemma evalBiv5_DX2 : evalBiv5 DX2_biv = DX2_5 := by
  simp only [DX2_biv, eS, eQ, evalBiv5, denote, ringEval, vSQT, DX2_5, u3_5]; ring

lemma evalBiv5_DY2 : evalBiv5 DY2_biv = DY2_5 := by
  simp only [DY2_biv, eT, evalBiv5, denote, ringEval, vSQT, DY2_5, v3_5]; ring

lemma evalBiv5_W2 : evalBiv5 W2_biv = W2_5 := by
  rw [W2_biv, evalBiv5_bivMul, evalBiv5, scale_denote]
  change (X 0 * X 2) * 1 * 1 * evalBiv5 DX2_biv * evalBiv5 DY2_biv = W2_5
  rw [evalBiv5_DX2, evalBiv5_DY2, W2_5]; ring

lemma evalBiv5_MA : evalBiv5 MA_biv = MA_5 := by
  rw [MA_biv, evalBiv5_bivMul, evalBiv5, scale_denote]
  simp only [evalBiv5, u3_5_biv, v3_5_biv, eS, eQ, eT, denote, ringEval, vSQT, MA_5, u3_5, v3_5]; ring

lemma evalBiv5_NA_Q : evalBiv5 NA_Q_biv = NA_Q5 := by
  rw [NA_Q_biv, evalBiv5_bivSub, evalBiv5_bivMul, evalBiv5_bivMul, evalBiv5_bivScale]
  have hE (p : Biv) : evalBiv5 (eRad_biv p) = E_rad (evalBiv5 p) := by
    rw [eRad_biv, evalBiv5_bivAdd]
    simp only [evalBiv5, scale_denote, ringEval, Int.cast_one, pow_zero, pow_one, one_mul, mul_one]
    rw [show denote vSQT (X 3) (X 4) (dx p) = evalBiv5 (dx p) from rfl,
        show denote vSQT (X 3) (X 4) (dy p) = evalBiv5 (dy p) from rfl,
        ← pderiv_evalBiv5_3, ← pderiv_evalBiv5_4, E_rad]; rfl
  rw [hE, hE, evalBiv5_W2, evalBiv5_MA, NA_Q5]
  have hC2 : C (σ := Fin 5) ((2 : ℤ) : ℂ) = 2 := by rw [Int.cast_ofNat, map_ofNat]
  rw [hC2]

-- THE CORE KERNEL-VERIFIED 5-VARIABLE POLYNOMIAL IDENTITY (< 2s!)
theorem vertical_poly5_identity : evalBiv5 vertLHS_biv = evalBiv5 vertRHS_biv := by
  apply HodgeComputer.Formal.KroneckerCheck.biv_denote_eq_of_kronecker3 vSQT (X 3) (X 4) 13 12 14 (2 ^ 80) vertLHS_biv vertRHS_biv
  decide +kernel

-- Helper: Poisson operator in Poly5 matching pois_biv
def poisson5 (u D : Poly5) (a b : Fin 5) : Poly5 :=
  2 * W2_5 * D * (pderiv a F5 * pderiv b u - pderiv b F5 * pderiv a u) -
  u * D * (pderiv a F5 * pderiv b W2_5 - pderiv b F5 * pderiv a W2_5) -
  2 * W2_5 * u * (pderiv a F5 * pderiv b D - pderiv b F5 * pderiv a D)

lemma evalBiv5_pois_scaled (ub : Biv) (a b : Fin 5) (negSign : Bool) :
    evalBiv5 (pois_biv ub H0_int_biv a.val b.val F5_int_biv negSign) =
      (if negSign then -1 else 1) * 49 * poisson5 (evalBiv5 ub) H0_5 a b := by
  dsimp only [pois_biv]
  have hbody :
      evalBiv5 (bivSub (bivSub
          (bivMul (bivMul (bivScale 2 W2_biv) H0_int_biv)
            (bivSub (bivMul (bivDeriv a.val F5_int_biv) (bivDeriv b.val ub))
                    (bivMul (bivDeriv b.val F5_int_biv) (bivDeriv a.val ub))))
          (bivMul (bivMul ub H0_int_biv)
            (bivSub (bivMul (bivDeriv a.val F5_int_biv) (bivDeriv b.val W2_biv))
                    (bivMul (bivDeriv b.val F5_int_biv) (bivDeriv a.val W2_biv)))))
        (bivMul (bivMul (bivScale 2 W2_biv) ub)
          (bivSub (bivMul (bivDeriv a.val F5_int_biv) (bivDeriv b.val H0_int_biv))
                  (bivMul (bivDeriv b.val F5_int_biv) (bivDeriv a.val H0_int_biv))))) =
      49 * poisson5 (evalBiv5 ub) H0_5 a b := by
    simp only [evalBiv5_bivSub, evalBiv5_bivMul, evalBiv5_bivScale, ← pderiv_evalBiv5,
      evalBiv5_W2, evalBiv5_H0_int, evalBiv5_F5_int]
    have h7 (p : Poly5) (i : Fin 5) : pderiv i (7 * p) = 7 * pderiv i p := by
      rw [Derivation.leibniz, pderiv_ofNat]; simp
    have hC2 : C (σ := Fin 5) ((2 : ℤ) : ℂ) = 2 := by rw [Int.cast_ofNat, map_ofNat]
    simp only [h7, hC2, poisson5]; ring
  cases negSign
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hbody]; ring
  · simp only [↓reduceIte]; rw [evalBiv5, negBiv_denote]; change -evalBiv5 _ = _; rw [hbody]; ring

private lemma pderiv_H0_3 : pderiv (3 : Fin 5) H0_5 = 0 := pderiv_3_poly4ToPoly5 H0_4

private lemma pderiv_H0_4 : pderiv (4 : Fin 5) H0_5 = 0 := by
  have h4 : pderiv (3 : Fin 4) H0_4 = 0 := by
    rw [H0_4, poly3ToPoly4]
    induction H0_3 using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
    | mul_X p i hp =>
      simp only [map_mul, eval₂Hom_X', Derivation.leibniz, hp, smul_eq_mul, mul_zero, add_zero]
      fin_cases i <;> simp [pderiv_X]
  simpa [H0_5, tanIdx] using pderiv_poly4ToPoly5 3 H0_4 ▸ congrArg poly4ToPoly5 h4

lemma evalBiv5_pois6 :
    evalBiv5 (pois_biv u6_biv (.cons (.num 1) 0 0 .nil) 4 3 F5_xy_biv false) =
      poisson5 (evalBiv5 u6_biv) 1 4 3 := by
  dsimp only [pois_biv]
  simp only [Bool.false_eq_true, ↓reduceIte, evalBiv5_bivSub, evalBiv5_bivMul, evalBiv5_bivScale]
  have h1 : evalBiv5 (.cons (.num 1) 0 0 .nil) = (1 : Poly5) := by simp [evalBiv5, denote, ringEval]
  have hbd3 (p : Biv) : evalBiv5 (bivDeriv 3 p) = pderiv (3 : Fin 5) (evalBiv5 p) := (pderiv_evalBiv5 3 p).symm
  have hbd4 (p : Biv) : evalBiv5 (bivDeriv 4 p) = pderiv (4 : Fin 5) (evalBiv5 p) := (pderiv_evalBiv5 4 p).symm
  have hd3 : evalBiv5 (bivDeriv 3 F5_xy_biv) = pderiv 3 F5 := by
    rw [hbd3, evalBiv5_F5_xy, F5, map_add (pderiv 3) _ H0_5, pderiv_H0_3, add_zero]
  have hd4 : evalBiv5 (bivDeriv 4 F5_xy_biv) = pderiv 4 F5 := by
    rw [hbd4, evalBiv5_F5_xy, F5, map_add (pderiv 4) _ H0_5, pderiv_H0_4, add_zero]
  have h1d3 : evalBiv5 (bivDeriv 3 (.cons (.num 1) 0 0 .nil)) = 0 := by
    rw [hbd3, h1, Derivation.map_one_eq_zero]
  have h1d4 : evalBiv5 (bivDeriv 4 (.cons (.num 1) 0 0 .nil)) = 0 := by
    rw [hbd4, h1, Derivation.map_one_eq_zero]
  rw [hd3, hd4, h1d3, h1d4, hbd3 u6_biv, hbd4 u6_biv, hbd3 W2_biv, hbd4 W2_biv, h1, evalBiv5_W2]
  have hC2 : C (σ := Fin 5) ((2 : ℤ) : ℂ) = 2 := by rw [Int.cast_ofNat, map_ofNat]
  rw [hC2, poisson5, Derivation.map_one_eq_zero, Derivation.map_one_eq_zero]


lemma resDivW_add (v w : Fin 4 → K5) : resDivW (v + w) = resDivW v + resDivW w := by
  simp only [resDivW, ← Finset.sum_add_distrib, Pi.add_apply, map_add]
  apply Finset.sum_congr rfl; intro i _; ring

private lemma pderiv_F5_comm (a b : Fin 5) : pderiv a (pderiv b F5) = pderiv b (pderiv a F5) := by
  induction F5 using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, pderiv_X, hp]
    have hc (u v : Fin 5) : pderiv u ((Pi.single v (1 : Poly5) : Fin 5 → Poly5) k) = 0 := by
      by_cases h : k = v
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    simp only [hc, mul_zero, zero_add]; ring

-- Three clean ResDiv_W component identities in K5
private lemma resDivW_comp_A (j : Fin 3) (u : Poly5) :
    let w : Fin 4 → K5 := fun i =>
      if i.val = j.val then -(toK5 (pderiv 4 F5) * toK5 u) / H0_K
      else if i = 3 then toK5 (pderiv (tanIdx ⟨j.val, by omega⟩) F5) * toK5 u / H0_K
      else 0
    2 * W2_K * H0_K ^ 2 * resDivW w = -toK5 (poisson5 u H0_5 4 (tanIdx ⟨j.val, by omega⟩)) := by
  intro w
  let j4 : Fin 4 := ⟨j.val, by omega⟩
  have hsum : resDivW w =
      (δ j4 (w j4) - w j4 * δ j4 Fx_K / Fx_K - w j4 * δ j4 W2_K / (2 * W2_K)) +
      (δ 3 (w 3) - w 3 * δ 3 Fx_K / Fx_K - w 3 * δ 3 W2_K / (2 * W2_K)) := by
    rw [resDivW, Fin.sum_univ_four]
    fin_cases j <;> simp [w, j4]
  have hwj : w j4 = -(toK5 (pderiv 4 F5) * toK5 u) / H0_K := by simp [w, j4]
  have hw3 : w 3 = toK5 (pderiv (tanIdx j4) F5) * toK5 u / H0_K := by
    have hne : (3 : ℕ) ≠ j.val := by omega
    simp [w, j4, hne]
  rw [hsum, hwj, hw3]
  have hFx_ne := Fx_K_ne_zero; have hW2_ne := W2_K_ne_zero; have hH0_ne := H0_K_ne_zero
  have hH0_eq : H0_K = toK5 H0_5 := (toK5_poly4 H0_4).symm
  dsimp only [Fx_K, W2_K] at hFx_ne hW2_ne
  rw [hH0_eq] at hH0_ne ⊢
  simp only [Derivation.leibniz_div, Derivation.leibniz, map_neg, smul_eq_mul,
    Fx_K, W2_K, δ_toK5, poisson5, map_sub, map_mul, map_ofNat]
  have hc1 := congrArg toK5 (pderiv_F5_comm (tanIdx j4) 4)
  have hc2 := congrArg toK5 (pderiv_F5_comm 3 4)
  have hc3 := congrArg toK5 (pderiv_F5_comm 3 (tanIdx j4))
  have hH3 : toK5 (pderiv 3 H0_5) = 0 := by rw [pderiv_H0_3, map_zero]
  have hH4 : toK5 (pderiv 4 H0_5) = 0 := by rw [pderiv_H0_4, map_zero]
  have htan3 : tanIdx (3 : Fin 4) = 4 := rfl
  simp only [htan3] at *
  rw [hc1, hc2, hc3, hH3, hH4]
  generalize toK5 u = uv
  generalize toK5 (pderiv (tanIdx j4) u) = uj; generalize toK5 (pderiv 3 u) = ux; generalize toK5 (pderiv 4 u) = uy
  generalize toK5 (pderiv (tanIdx j4) F5) = fj; generalize toK5 (pderiv 3 F5) = fx at hFx_ne ⊢
  generalize toK5 (pderiv 4 F5) = fy
  generalize toK5 (pderiv 4 (pderiv (tanIdx j4) F5)) = fjy
  generalize toK5 (pderiv 4 (pderiv 3 F5)) = fxy
  generalize toK5 (pderiv (tanIdx j4) (pderiv 3 F5)) = fjx
  generalize toK5 (pderiv 3 (pderiv 3 F5)) = fxx
  generalize toK5 W2_5 = w2 at hW2_ne ⊢
  generalize toK5 (pderiv (tanIdx j4) W2_5) = wj; generalize toK5 (pderiv 3 W2_5) = wx; generalize toK5 (pderiv 4 W2_5) = wy
  generalize toK5 H0_5 = h0 at hH0_ne ⊢; generalize toK5 (pderiv (tanIdx j4) H0_5) = hj
  field_simp [hFx_ne, hW2_ne, hH0_ne]; ring

private lemma resDivW_comp_B (j : Fin 3) (u : Poly5) :
    let w : Fin 4 → K5 := fun i =>
      if i.val = j.val then Fx_K * toK5 u / H0_K else 0
    2 * W2_K * H0_K ^ 2 * resDivW w = toK5 (poisson5 u H0_5 3 (tanIdx ⟨j.val, by omega⟩)) := by
  intro w
  let j4 : Fin 4 := ⟨j.val, by omega⟩
  have hsum : resDivW w =
      δ j4 (w j4) - w j4 * δ j4 Fx_K / Fx_K - w j4 * δ j4 W2_K / (2 * W2_K) := by
    rw [resDivW, Fin.sum_univ_four]
    fin_cases j <;> simp [w, j4]
  have hwj : w j4 = Fx_K * toK5 u / H0_K := by simp [w, j4]
  rw [hsum, hwj]
  have hFx_ne := Fx_K_ne_zero; have hW2_ne := W2_K_ne_zero; have hH0_ne := H0_K_ne_zero
  have hH0_eq : H0_K = toK5 H0_5 := (toK5_poly4 H0_4).symm
  dsimp only [Fx_K, W2_K] at hFx_ne hW2_ne
  rw [hH0_eq] at hH0_ne ⊢
  simp only [Derivation.leibniz_div, Derivation.leibniz, smul_eq_mul, Fx_K, W2_K, δ_toK5,
    poisson5, map_sub, map_mul, map_ofNat]
  have hH3 : toK5 (pderiv 3 H0_5) = 0 := by rw [pderiv_H0_3, map_zero]
  rw [hH3]
  generalize toK5 u = uv
  generalize toK5 (pderiv (tanIdx j4) u) = uj; generalize toK5 (pderiv 3 u) = ux
  generalize toK5 (pderiv (tanIdx j4) F5) = fj; generalize toK5 (pderiv 3 F5) = fx at hFx_ne ⊢
  generalize toK5 (pderiv (tanIdx j4) (pderiv 3 F5)) = fjx; generalize toK5 (pderiv 3 (pderiv 3 F5)) = fxx
  generalize toK5 W2_5 = w2 at hW2_ne ⊢
  generalize toK5 (pderiv (tanIdx j4) W2_5) = wj; generalize toK5 (pderiv 3 W2_5) = wx
  generalize toK5 H0_5 = h0 at hH0_ne ⊢; generalize toK5 (pderiv (tanIdx j4) H0_5) = hj
  field_simp [hFx_ne, hW2_ne, hH0_ne]; ring

private lemma resDivW_comp_C (u : Poly5) :
    let w : Fin 4 → K5 := fun i => if i = 3 then -(Fx_K * toK5 u / H0_K ^ 2) else 0
    2 * W2_K * H0_K ^ 2 * resDivW w = toK5 (poisson5 u 1 4 3) := by
  intro w
  have hsum : resDivW w =
      δ 3 (w 3) - w 3 * δ 3 Fx_K / Fx_K - w 3 * δ 3 W2_K / (2 * W2_K) := by
    rw [resDivW, Fin.sum_univ_four]; simp [w]
  have hw3 : w 3 = -(Fx_K * toK5 u / H0_K ^ 2) := by simp [w]
  rw [hsum, hw3]
  have hFx_ne := Fx_K_ne_zero; have hW2_ne := W2_K_ne_zero; have hH0_ne := H0_K_ne_zero
  have hH0_eq : H0_K = toK5 H0_5 := (toK5_poly4 H0_4).symm
  dsimp only [Fx_K, W2_K] at hFx_ne hW2_ne
  rw [hH0_eq] at hH0_ne ⊢
  simp only [map_neg, Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, nsmul_eq_mul, Fx_K, W2_K, δ_toK5, poisson5, map_sub, map_mul, map_one,
    map_ofNat, Derivation.map_one_eq_zero, map_zero]
  have htan3 : tanIdx (3 : Fin 4) = 4 := rfl
  simp only [htan3]
  have hH3 : toK5 (pderiv 3 H0_5) = 0 := by rw [pderiv_H0_3, map_zero]
  have hH4 : toK5 (pderiv 4 H0_5) = 0 := by rw [pderiv_H0_4, map_zero]
  rw [hH3, hH4]
  generalize toK5 u = uv; generalize toK5 (pderiv 3 u) = ux; generalize toK5 (pderiv 4 u) = uy
  generalize toK5 (pderiv 3 F5) = fx at hFx_ne ⊢; generalize toK5 (pderiv 4 F5) = fy
  generalize toK5 (pderiv 4 (pderiv 3 F5)) = fxy; generalize toK5 (pderiv 3 (pderiv 3 F5)) = fxx
  generalize toK5 W2_5 = w2 at hW2_ne ⊢
  generalize toK5 (pderiv 3 W2_5) = wx; generalize toK5 (pderiv 4 W2_5) = wy
  generalize toK5 H0_5 = h0 at hH0_ne ⊢
  field_simp [hFx_ne, hW2_ne, hH0_ne]; ring

-- Main Vertical Identity Theorem in K5!
theorem vertical_K5_identity :
    2 * W2_K * H0_K ^ 2 * resDivW w_V + toK5 P_horiz_5 = toK5 NA_Q5 * H0_K := by
  let wA0 : Fin 4 → K5 := fun i => if i.val = 0 then -(toK5 (pderiv 4 F5) * toK5 (uPoly 0)) / H0_K else if i = 3 then toK5 (pderiv 0 F5) * toK5 (uPoly 0) / H0_K else 0
  let wA1 : Fin 4 → K5 := fun i => if i.val = 1 then -(toK5 (pderiv 4 F5) * toK5 (uPoly 1)) / H0_K else if i = 3 then toK5 (pderiv 1 F5) * toK5 (uPoly 1) / H0_K else 0
  let wA2 : Fin 4 → K5 := fun i => if i.val = 2 then -(toK5 (pderiv 4 F5) * toK5 (uPoly 2)) / H0_K else if i = 3 then toK5 (pderiv 2 F5) * toK5 (uPoly 2) / H0_K else 0
  let wB0 : Fin 4 → K5 := fun i => if i.val = 0 then Fx_K * toK5 (uPoly 3) / H0_K else 0
  let wB1 : Fin 4 → K5 := fun i => if i.val = 1 then Fx_K * toK5 (uPoly 4) / H0_K else 0
  let wB2 : Fin 4 → K5 := fun i => if i.val = 2 then Fx_K * toK5 (uPoly 5) / H0_K else 0
  let wC  : Fin 4 → K5 := fun i => if i = 3 then -(Fx_K * toK5 (uPoly 6) / H0_K ^ 2) else 0
  have hwV_split : w_V = wA0 + wA1 + wA2 + wB0 + wB1 + wB2 + wC := by
    ext i; fin_cases i <;> simp [w_V, wA0, wA1, wA2, wB0, wB1, wB2, wC] <;> ring
  have hdivV : 2 * W2_K * H0_K ^ 2 * resDivW w_V =
      -toK5 (poisson5 (uPoly 0) H0_5 4 0) - toK5 (poisson5 (uPoly 1) H0_5 4 1) -
      toK5 (poisson5 (uPoly 2) H0_5 4 2) + toK5 (poisson5 (uPoly 3) H0_5 3 0) +
      toK5 (poisson5 (uPoly 4) H0_5 3 1) + toK5 (poisson5 (uPoly 5) H0_5 3 2) +
      toK5 (poisson5 (uPoly 6) 1 4 3) := by
    rw [hwV_split, resDivW_add, resDivW_add, resDivW_add, resDivW_add, resDivW_add, resDivW_add]
    have h0 : 2 * W2_K * H0_K ^ 2 * resDivW wA0 = -toK5 (poisson5 (uPoly 0) H0_5 4 0) :=
      resDivW_comp_A 0 (uPoly 0)
    have h1 : 2 * W2_K * H0_K ^ 2 * resDivW wA1 = -toK5 (poisson5 (uPoly 1) H0_5 4 1) :=
      resDivW_comp_A 1 (uPoly 1)
    have h2 : 2 * W2_K * H0_K ^ 2 * resDivW wA2 = -toK5 (poisson5 (uPoly 2) H0_5 4 2) :=
      resDivW_comp_A 2 (uPoly 2)
    have h3 : 2 * W2_K * H0_K ^ 2 * resDivW wB0 = toK5 (poisson5 (uPoly 3) H0_5 3 0) :=
      resDivW_comp_B 0 (uPoly 3)
    have h4 : 2 * W2_K * H0_K ^ 2 * resDivW wB1 = toK5 (poisson5 (uPoly 4) H0_5 3 1) :=
      resDivW_comp_B 1 (uPoly 4)
    have h5 : 2 * W2_K * H0_K ^ 2 * resDivW wB2 = toK5 (poisson5 (uPoly 5) H0_5 3 2) :=
      resDivW_comp_B 2 (uPoly 5)
    have h6 : 2 * W2_K * H0_K ^ 2 * resDivW wC = toK5 (poisson5 (uPoly 6) 1 4 3) :=
      resDivW_comp_C (uPoly 6)
    linear_combination h0 + h1 + h2 + h3 + h4 + h5 + h6
  have hid := congrArg toK5 vertical_poly5_identity
  have hRHS0 : toK5 (evalBiv5 vertRHS_biv) = 0 := by
    rw [vertRHS_biv, evalBiv5_bivMul, evalBiv5_bivScale, evalBiv5_F5_int,
      map_mul, map_mul, map_mul, map_ofNat, toK5_F5, mul_zero, mul_zero]
  rw [hRHS0] at hid
  have hpois_C (c : ℂ) (u D : Poly5) (a b : Fin 5) :
      poisson5 (C c * u) D a b = C c * poisson5 u D a b := by
    simp only [poisson5, Derivation.leibniz, pderiv_C, smul_eq_mul, mul_zero]; ring
  have hLHS_expand : evalBiv5 vertLHS_biv =
      C (D_all : ℂ) * (NA_Q5 * H0_5 -
        (-poisson5 (uPoly 0) H0_5 4 0 - poisson5 (uPoly 1) H0_5 4 1 - poisson5 (uPoly 2) H0_5 4 2 +
         poisson5 (uPoly 3) H0_5 3 0 + poisson5 (uPoly 4) H0_5 3 1 + poisson5 (uPoly 5) H0_5 3 2 +
         poisson5 (uPoly 6) 1 4 3) - P_horiz_5) := by
    have hD1 : (D_all : ℂ) = 7 * (D_u6 : ℂ) := by norm_num [D_all, D_u6]
    have hD2 : (D_all : ℂ) = 7 * 49 * (D_u05 : ℂ) := by norm_num [D_all, D_u05]
    have hD3 : (D_all : ℂ) = 12 * (D_P : ℂ) := by norm_num [D_all, D_P]
    have hD_u05_ne : (D_u05 : ℂ) ≠ 0 := by norm_num [D_u05]
    have hD_u6_ne  : (D_u6  : ℂ) ≠ 0 := by norm_num [D_u6]
    have hD_P_ne   : (D_P   : ℂ) ≠ 0 := by norm_num [D_P]
    have hcu05 : C (σ := Fin 5) (D_all : ℂ) * C (1 / (D_u05 : ℂ)) = C (7 * 49 : ℂ) := by
      rw [← map_mul, hD2]; congr 1; field_simp [hD_u05_ne]
    have hcu6 : C (σ := Fin 5) (D_all : ℂ) * C (1 / (D_u6 : ℂ)) = C (7 : ℂ) := by
      rw [← map_mul, hD1]; congr 1; field_simp [hD_u6_ne]
    have hcP : C (σ := Fin 5) (D_all : ℂ) * C (1 / (D_P : ℂ)) = C (12 : ℂ) := by
      rw [← map_mul, hD3]; congr 1; field_simp [hD_P_ne]
    rw [vertLHS_biv, evalBiv5_bivSub, evalBiv5_bivSub, evalBiv5_bivMul,
      evalBiv5_bivScale, evalBiv5_bivScale, evalBiv5_bivScale, evalBiv5_NA_Q, evalBiv5_H0_int]
    have hdV : evalBiv5 dV_int_biv =
        49 * (-poisson5 (evalBiv5 u0_biv) H0_5 4 0 - poisson5 (evalBiv5 u1_biv) H0_5 4 1 -
          poisson5 (evalBiv5 u2_biv) H0_5 4 2 + poisson5 (evalBiv5 u3_biv) H0_5 3 0 +
          poisson5 (evalBiv5 u4_biv) H0_5 3 1 + poisson5 (evalBiv5 u5_biv) H0_5 3 2) +
        poisson5 (evalBiv5 u6_biv) 1 4 3 := by
      simp only [dV_int_biv, evalBiv5_bivAdd]
      have hp0 := evalBiv5_pois_scaled u0_biv 4 0 true
      have hp1 := evalBiv5_pois_scaled u1_biv 4 1 true
      have hp2 := evalBiv5_pois_scaled u2_biv 4 2 true
      have hp3 := evalBiv5_pois_scaled u3_biv 3 0 false
      have hp4 := evalBiv5_pois_scaled u4_biv 3 1 false
      have hp5 := evalBiv5_pois_scaled u5_biv 3 2 false
      change evalBiv5 (pois_biv u0_biv H0_int_biv (4 : Fin 5).val (0 : Fin 5).val F5_int_biv true) +
        evalBiv5 (pois_biv u1_biv H0_int_biv (4 : Fin 5).val (1 : Fin 5).val F5_int_biv true) +
        (evalBiv5 (pois_biv u2_biv H0_int_biv (4 : Fin 5).val (2 : Fin 5).val F5_int_biv true) +
        evalBiv5 (pois_biv u3_biv H0_int_biv (3 : Fin 5).val (0 : Fin 5).val F5_int_biv false)) +
        (evalBiv5 (pois_biv u4_biv H0_int_biv (3 : Fin 5).val (1 : Fin 5).val F5_int_biv false) +
        evalBiv5 (pois_biv u5_biv H0_int_biv (3 : Fin 5).val (2 : Fin 5).val F5_int_biv false) +
        evalBiv5 (pois_biv u6_biv (.cons (.num 1) 0 0 .nil) 4 3 F5_xy_biv false)) = _
      rw [hp0, hp1, hp2, hp3, hp4, hp5, evalBiv5_pois6]
      simp only [Bool.false_eq_true, ↓reduceIte]; ring
    rw [hdV, P_horiz_5]
    simp only [uPoly, hpois_C]
    have h7D : C (σ := Fin 5) (D_all : ℂ) = 7 * C (D_u6 : ℂ) := by
      rw [hD1, map_mul, map_ofNat]
    have hC12 : C (σ := Fin 5) ((12 : ℤ) : ℂ) = C (12 : ℂ) := by rw [Int.cast_ofNat]
    have hC7 : C (σ := Fin 5) ((7 : ℤ) : ℂ) = C (7 : ℂ) := by rw [Int.cast_ofNat]
    have hC749 : C (σ := Fin 5) ((7 : ℤ) : ℂ) * 49 = C (7 * 49 : ℂ) := by
      rw [Int.cast_ofNat, ← map_ofNat C 49, ← map_mul]
    calc
      C (D_u6 : ℂ) * NA_Q5 * (7 * H0_5) -
          C ((7 : ℤ) : ℂ) * (49 * (-poisson5 (evalBiv5 u0_biv) H0_5 4 0 - poisson5 (evalBiv5 u1_biv) H0_5 4 1 -
            poisson5 (evalBiv5 u2_biv) H0_5 4 2 + poisson5 (evalBiv5 u3_biv) H0_5 3 0 +
            poisson5 (evalBiv5 u4_biv) H0_5 3 1 + poisson5 (evalBiv5 u5_biv) H0_5 3 2) +
            poisson5 (evalBiv5 u6_biv) 1 4 3) - C ((12 : ℤ) : ℂ) * evalBiv5 P_horiz_biv
        = (7 * C (D_u6 : ℂ)) * (NA_Q5 * H0_5) -
            (C ((7 : ℤ) : ℂ) * 49) * (-poisson5 (evalBiv5 u0_biv) H0_5 4 0 - poisson5 (evalBiv5 u1_biv) H0_5 4 1 -
              poisson5 (evalBiv5 u2_biv) H0_5 4 2 + poisson5 (evalBiv5 u3_biv) H0_5 3 0 +
              poisson5 (evalBiv5 u4_biv) H0_5 3 1 + poisson5 (evalBiv5 u5_biv) H0_5 3 2) -
            C ((7 : ℤ) : ℂ) * poisson5 (evalBiv5 u6_biv) 1 4 3 -
            C ((12 : ℤ) : ℂ) * evalBiv5 P_horiz_biv := by ring
      _ = C (D_all : ℂ) * (NA_Q5 * H0_5) -
            (C (D_all : ℂ) * C (1 / (D_u05 : ℂ))) * (-poisson5 (evalBiv5 u0_biv) H0_5 4 0 -
              poisson5 (evalBiv5 u1_biv) H0_5 4 1 - poisson5 (evalBiv5 u2_biv) H0_5 4 2 +
              poisson5 (evalBiv5 u3_biv) H0_5 3 0 + poisson5 (evalBiv5 u4_biv) H0_5 3 1 +
              poisson5 (evalBiv5 u5_biv) H0_5 3 2) -
            (C (D_all : ℂ) * C (1 / (D_u6 : ℂ))) * poisson5 (evalBiv5 u6_biv) 1 4 3 -
            (C (D_all : ℂ) * C (1 / (D_P : ℂ))) * evalBiv5 P_horiz_biv := by
          rw [← h7D, hC749, ← hcu05, hC7, ← hcu6, hC12, ← hcP]
      _ = _ := by ring
  rw [hLHS_expand, map_mul] at hid
  have hDall_K_ne : toK5 (C (D_all : ℂ)) ≠ 0 := by
    have hne : (D_all : ℂ) ≠ 0 := by norm_num [D_all]
    intro h0
    have h1 : toK5 (C (D_all : ℂ)) * toK5 (C ((D_all : ℂ)⁻¹)) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hne, map_one, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hzero := (mul_eq_zero.mp hid).resolve_left hDall_K_ne
  simp only [map_sub, map_add, map_neg, map_mul] at hzero
  have hH0_eq : toK5 H0_5 = H0_K := toK5_poly4 H0_4
  rw [hH0_eq] at hzero
  linear_combination -hzero + hdivV

end SymmetricSexticResidual.VerticalIdentity

theorem solution :
    2 * SymmetricSexticResidual.K5Field.W2_K * SymmetricSexticResidual.K5Field.H0_K ^ 2 *
      SymmetricSexticResidual.K5Field.resDivW SymmetricSexticResidual.VerticalIdentity.w_V +
      SymmetricSexticResidual.K5Field.toK5 SymmetricSexticResidual.VerticalIdentity.P_horiz_5 =
    SymmetricSexticResidual.K5Field.toK5 SymmetricSexticResidual.K5Field.NA_Q5 *
      SymmetricSexticResidual.K5Field.H0_K :=
  SymmetricSexticResidual.VerticalIdentity.vertical_K5_identity
