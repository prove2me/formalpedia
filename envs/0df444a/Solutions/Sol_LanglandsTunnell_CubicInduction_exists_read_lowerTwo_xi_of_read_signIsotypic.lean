-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_read_lowerTwo_xi_of_read_signIsotypic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d9b8498f-4f31-56ee-a4f1-950be0a788dc

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_forall_det_pow_mul_eval_sum_quadric_mul_columnRealisation_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasDerivAt_archFlow_eq_eval_inducedPicture_act_of_upperTriangular_equivariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_pderiv_pderiv_eq_half_eval_realise_lowerTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_read_lowerTwo_xi_of_read_signIsotypic

set_option autoImplicit false

namespace WsB
namespace C6

open MvPolynomial

noncomputable section

abbrev R3 := MvPolynomial (Fin 3) ℂ
abbrev R9 := MvPolynomial (Fin 3 × Fin 3) ℂ

theorem pderiv_comm (i j : Fin 3) (p : R3) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have h : ⁅(pderiv i : Derivation ℂ R3 R3), (pderiv j : Derivation ℂ R3 R3)⁆ = 0 := by
    refine MvPolynomial.derivation_ext (fun k => ?_)
    rw [Derivation.commutator_apply]
    classical
    simp only [pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℂ R3 R3 => D p) h
  simp only [Derivation.commutator_apply] at h2
  have h3 : pderiv i (pderiv j p) - pderiv j (pderiv i p) = 0 := by simpa using h2
  exact sub_eq_zero.mp h3

theorem sort10 (q : R3) : pderiv 0 (pderiv 1 q) = pderiv 1 (pderiv 0 q) := pderiv_comm 0 1 q
theorem sort20 (q : R3) : pderiv 0 (pderiv 2 q) = pderiv 2 (pderiv 0 q) := pderiv_comm 0 2 q
theorem sort21 (q : R3) : pderiv 1 (pderiv 2 q) = pderiv 2 (pderiv 1 q) := pderiv_comm 1 2 q

theorem max01 : max (0 : Fin 3) 1 = 1 := by decide
theorem max10 : max (1 : Fin 3) 0 = 1 := by decide
theorem max02 : max (0 : Fin 3) 2 = 2 := by decide
theorem max20 : max (2 : Fin 3) 0 = 2 := by decide
theorem max12 : max (1 : Fin 3) 2 = 2 := by decide
theorem max21 : max (2 : Fin 3) 1 = 2 := by decide
theorem min01 : min (0 : Fin 3) 1 = 0 := by decide
theorem min10 : min (1 : Fin 3) 0 = 0 := by decide
theorem min02 : min (0 : Fin 3) 2 = 0 := by decide
theorem min20 : min (2 : Fin 3) 0 = 0 := by decide
theorem min12 : min (1 : Fin 3) 2 = 1 := by decide
theorem min21 : min (2 : Fin 3) 1 = 1 := by decide
theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
theorem ne10 : (1 : Fin 3) ≠ 0 := by decide
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
theorem ne20 : (2 : Fin 3) ≠ 0 := by decide
theorem ne12 : (1 : Fin 3) ≠ 2 := by decide
theorem ne21 : (2 : Fin 3) ≠ 1 := by decide
theorem lt01 : (0 : Fin 3) < 1 := by decide
theorem lt02 : (0 : Fin 3) < 2 := by decide
theorem lt12 : (1 : Fin 3) < 2 := by decide
theorem nlt10 : ¬ (1 : Fin 3) < 0 := by decide
theorem nlt20 : ¬ (2 : Fin 3) < 0 := by decide
theorem nlt21 : ¬ (2 : Fin 3) < 1 := by decide
theorem nlt00 : ¬ (0 : Fin 3) < 0 := by decide
theorem nlt11 : ¬ (1 : Fin 3) < 1 := by decide
theorem nlt22 : ¬ (2 : Fin 3) < 2 := by decide
theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide

theorem rho0 : (![1, 0, -1] : Fin 3 → ℂ) 0 = 1 := rfl
theorem rho1 : (![1, 0, -1] : Fin 3 → ℂ) 1 = 0 := rfl
theorem rho2 : (![1, 0, -1] : Fin 3 → ℂ) 2 = -1 := rfl

def Xi (ν : Fin 3 → ℂ) (p : R3) : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
  Matrix.of fun c d =>
    if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
    else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
      MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)

def lower2 (M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)) : MvPolynomial (Fin 3) ℂ :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))

def realise (j : Fin 3) (q : R3) : R9 :=
  MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q

def act (ν : Fin 3 → ℂ) (c d : Fin 3) (p : R9) : R9 :=
  (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
      (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
  ∑ i : Fin 3, ∑ j : Fin 3,
    (∑ m : Fin 3,
      (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
        else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
        else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
      MvPolynomial.pderiv (i, j) p

def Mlt (ν : Fin 3 → ℂ) (c d : Fin 3) : R9 :=
  ∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
      (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))

def Vf (c d i j : Fin 3) : R9 :=
  ∑ m : Fin 3,
    (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
      else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
      else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)

def Dop (c d : Fin 3) (p : R9) : R9 :=
  ∑ i : Fin 3, ∑ j : Fin 3, Vf c d i j * MvPolynomial.pderiv (i, j) p

theorem act_eq (ν : Fin 3 → ℂ) (c d : Fin 3) (p : R9) : act ν c d p = Mlt ν c d * p + Dop c d p := rfl

theorem Xi_diag (ν : Fin 3 → ℂ) (p : R3) (c : Fin 3) :
    Xi ν p c c = C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p := by
  simp [Xi]

theorem Xi_off (ν : Fin 3 → ℂ) (p : R3) (c d : Fin 3) (h : c ≠ d) :
    Xi ν p c d = -(X (max c d) * pderiv (min c d) p - X (min c d) * pderiv (max c d) p) := by
  simp [Xi, h]

theorem lower2_Xi (ν : Fin 3 → ℂ) (p : R3) :
    lower2 (Xi ν p) =
      C (2 * (ν 0 - 1)) * pderiv 0 (pderiv 0 p) + C (2 * ν 1) * pderiv 1 (pderiv 1 p)
        + C (2 * (ν 2 + 1)) * pderiv 2 (pderiv 2 p)
      + C 2 * (X 0 * pderiv 1 (pderiv 1 (pderiv 0 p)) - X 1 * pderiv 1 (pderiv 0 (pderiv 0 p)))
      + C 2 * (X 0 * pderiv 2 (pderiv 2 (pderiv 0 p)) - X 2 * pderiv 2 (pderiv 0 (pderiv 0 p)))
      + C 2 * (X 1 * pderiv 2 (pderiv 2 (pderiv 1 p)) - X 2 * pderiv 2 (pderiv 1 (pderiv 1 p))) := by
  simp only [lower2, Fin.sum_univ_three]
  rw [Xi_diag, Xi_diag, Xi_diag, Xi_off ν p 0 1 ne01, Xi_off ν p 0 2 ne02, Xi_off ν p 1 0 ne10,
    Xi_off ν p 1 2 ne12, Xi_off ν p 2 0 ne20, Xi_off ν p 2 1 ne21]
  simp only [max01, max10, max02, max20, max12, max21, min01, min10, min02, min20, min12, min21,
    map_add, map_sub, map_neg, pderiv_mul, pderiv_C, pderiv_X_self,
    pderiv_X_of_ne ne01, pderiv_X_of_ne ne10, pderiv_X_of_ne ne02, pderiv_X_of_ne ne20,
    pderiv_X_of_ne ne12, pderiv_X_of_ne ne21, zero_mul, one_mul, zero_add, sort10, sort20, sort21]
  simp only [rho0, rho1, rho2, map_mul, map_add, map_sub, map_neg, map_ofNat, map_one, add_zero]
  ring

theorem realise_eq (j : Fin 3) (q : R3) : realise j q = rename (fun a : Fin 3 => (a, j)) q := by
  rw [MvPolynomial.rename_eq_aeval]; rfl

theorem eval_realise (k : Fin 3 × Fin 3 → ℂ) (j : Fin 3) (q : R3) :
    eval k (realise j q) = eval (fun a => k (a, j)) q := by
  rw [realise_eq, eval_rename]; rfl

theorem pderiv_realise_self (i j : Fin 3) (q : R3) :
    pderiv (i, j) (realise j q) = realise j (pderiv i q) := by
  rw [realise_eq, realise_eq]
  exact pderiv_rename (f := fun a : Fin 3 => (a, j)) (fun a b h => congrArg Prod.fst h) i q

theorem pderiv_realise_ne (i j j' : Fin 3) (h : j' ≠ j) (q : R3) :
    pderiv (i, j') (realise j q) = 0 := by
  classical
  rw [realise_eq]
  apply pderiv_eq_zero_of_notMem_vars
  intro hm
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (vars_rename _ _ hm)
  exact h (congrArg Prod.snd ha).symm

theorem Dop_mul (c d : Fin 3) (P Q : R9) : Dop c d (P * Q) = Dop c d P * Q + P * Dop c d Q := by
  simp only [Dop, pderiv_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem Dop_X (c d i j : Fin 3) : Dop c d (X (i, j)) = Vf c d i j := by
  unfold Dop
  rw [Fintype.sum_eq_single i (fun i' hi' => ?_)]
  · rw [Fintype.sum_eq_single j (fun j' hj' => ?_)]
    · rw [pderiv_X_self, mul_one]
    · rw [pderiv_X_of_ne (fun h => hj' (congrArg Prod.snd h).symm), mul_zero]
  · refine Finset.sum_eq_zero (fun j' _ => ?_)
    rw [pderiv_X_of_ne (fun h => hi' (congrArg Prod.fst h).symm), mul_zero]

theorem Dop_realise (c d j : Fin 3) (q : R3) :
    Dop c d (realise j q) = ∑ i : Fin 3, Vf c d i j * realise j (pderiv i q) := by
  unfold Dop
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_eq_single j (fun j' hj' => ?_)]
  · rw [pderiv_realise_self]
  · rw [pderiv_realise_ne i j j' hj', mul_zero]

theorem eval_Mlt (ν : Fin 3 → ℂ) (k : Fin 3 × Fin 3 → ℂ) (c d : Fin 3) :
    eval k (Mlt ν c d) = ∑ e : Fin 3, (ν e + (![1, 0, -1] : Fin 3 → ℂ) e) * (k (e, c) * k (e, d)) := by
  simp only [Mlt, map_sum, map_mul, eval_C, eval_X]

theorem eval_Vf (k : Fin 3 × Fin 3 → ℂ) (c d i j : Fin 3) :
    eval k (Vf c d i j) = ∑ m : Fin 3,
      (if m < i then k (i, c) * k (m, d) else if i < m then -(k (m, c) * k (i, d)) else 0) * k (m, j) := by
  simp only [Vf, map_sum, map_mul, eval_X, apply_ite (eval k), map_neg, map_zero]

theorem eval_act (ν : Fin 3 → ℂ) (k : Fin 3 × Fin 3 → ℂ) (c d i c' i' d' j : Fin 3) (q : R3) :
    eval k (act ν c d (X (i, c') * X (i', d') * realise j q)) =
      eval k (Mlt ν c d) * (k (i, c') * k (i', d') * eval (fun a => k (a, j)) q)
      + eval k (Vf c d i c') * k (i', d') * eval (fun a => k (a, j)) q
      + k (i, c') * eval k (Vf c d i' d') * eval (fun a => k (a, j)) q
      + k (i, c') * k (i', d') *
          ∑ l : Fin 3, eval k (Vf c d l j) * eval (fun a => k (a, j)) (pderiv l q) := by
  rw [act_eq, Dop_mul, Dop_mul, Dop_X, Dop_X, Dop_realise]
  simp only [map_add, map_mul, eval_X, eval_realise, map_sum, Finset.mul_sum]
  ring

def G (k : Fin 3 × Fin 3 → ℂ) (r s : Fin 3) : ℂ := ∑ a : Fin 3, k (r, a) * k (s, a)

set_option maxHeartbeats 16000000 in

theorem contr_AB (ν : Fin 3 → ℂ) (k : Fin 3 × Fin 3 → ℂ) (i i' j : Fin 3) (q : R3) :
    (∑ a : Fin 3, ∑ b : Fin 3, eval k (act ν a b (X (i, a) * X (i', b) * realise j q))) =
      (∑ e : Fin 3, (ν e + (![1, 0, -1] : Fin 3 → ℂ) e) * (G k e i * G k e i')) *
          eval (fun a => k (a, j)) q
      + (∑ m : Fin 3, (if m < i then G k i m * G k m i' else if i < m then -(G k m m * G k i i') else 0)) *
          eval (fun a => k (a, j)) q
      + (∑ m : Fin 3, (if m < i' then G k i' i * G k m m else if i' < m then -(G k m i * G k i' m) else 0)) *
          eval (fun a => k (a, j)) q
      + ∑ l : Fin 3, (∑ m : Fin 3, (if m < l then G k l i * G k m i'
          else if l < m then -(G k m i * G k l i') else 0) * k (m, j)) *
          eval (fun a => k (a, j)) (pderiv l q) := by
  simp only [eval_act, eval_Mlt, eval_Vf, G]
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases i' with rfl | rfl | rfl <;>
    (simp only [Fin.sum_univ_three, lt01, lt02, lt12,
        nlt10, nlt20, nlt21, lt_self_iff_false, if_true, if_false]; ring)

set_option maxHeartbeats 16000000 in

theorem contr_BA (ν : Fin 3 → ℂ) (k : Fin 3 × Fin 3 → ℂ) (i i' j : Fin 3) (q : R3) :
    (∑ a : Fin 3, ∑ b : Fin 3, eval k (act ν b a (X (i, a) * X (i', b) * realise j q))) =
      (∑ e : Fin 3, (ν e + (![1, 0, -1] : Fin 3 → ℂ) e) * (G k e i * G k e i')) *
          eval (fun a => k (a, j)) q
      + (∑ m : Fin 3, (if m < i then G k m m * G k i i' else if i < m then -(G k i m * G k m i') else 0)) *
          eval (fun a => k (a, j)) q
      + (∑ m : Fin 3, (if m < i' then G k m i * G k i' m else if i' < m then -(G k i' i * G k m m) else 0)) *
          eval (fun a => k (a, j)) q
      + ∑ l : Fin 3, (∑ m : Fin 3, (if m < l then G k m i * G k l i'
          else if l < m then -(G k l i * G k m i') else 0) * k (m, j)) *
          eval (fun a => k (a, j)) (pderiv l q) := by
  simp only [eval_act, eval_Mlt, eval_Vf, G]
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases i' with rfl | rfl | rfl <;>
    (simp only [Fin.sum_univ_three, lt01, lt02, lt12,
        nlt10, nlt20, nlt21, lt_self_iff_false, if_true, if_false]; ring)

theorem sum4_comm (g : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3, g a b i i') =
      ∑ i : Fin 3, ∑ i' : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, g a b i i' := by
  simp only [Fin.sum_univ_three]; ring

theorem Dop_add (c d : Fin 3) (P Q : R9) : Dop c d (P + Q) = Dop c d P + Dop c d Q := by
  simp only [Dop, map_add, mul_add, Finset.sum_add_distrib]

theorem Dop_C (c d : Fin 3) (r : ℂ) : Dop c d (C r) = 0 := by
  simp only [Dop, pderiv_C, mul_zero, Finset.sum_const_zero]

theorem act_symtwist (ν : Fin 3 → ℂ) (c d : Fin 3) (r : ℂ) (A B R : R9) :
    act ν c d (C r * (A + B) * R) = C r * act ν c d (A * R) + C r * act ν c d (B * R) := by
  rw [act_eq, act_eq, act_eq, Dop_mul, Dop_mul, Dop_add, Dop_mul, Dop_mul, Dop_C]
  ring

theorem contr_AB' (ν : Fin 3 → ℂ) (k : Fin 3 × Fin 3 → ℂ) (i i' j : Fin 3) (q : R3) :
    (∑ a : Fin 3, ∑ b : Fin 3, eval k (act ν a b (X (i, b) * X (i', a) * realise j q))) =
      (∑ e : Fin 3, (ν e + (![1, 0, -1] : Fin 3 → ℂ) e) * (G k e i * G k e i')) *
          eval (fun a => k (a, j)) q
      + (∑ m : Fin 3, (if m < i then G k m m * G k i i' else if i < m then -(G k i m * G k m i') else 0)) *
          eval (fun a => k (a, j)) q
      + (∑ m : Fin 3, (if m < i' then G k m i * G k i' m else if i' < m then -(G k i' i * G k m m) else 0)) *
          eval (fun a => k (a, j)) q
      + ∑ l : Fin 3, (∑ m : Fin 3, (if m < l then G k m i * G k l i'
          else if l < m then -(G k l i * G k m i') else 0) * k (m, j)) *
          eval (fun a => k (a, j)) (pderiv l q) := by
  rw [Finset.sum_comm]; exact contr_BA ν k i i' j q

theorem contr_BA' (ν : Fin 3 → ℂ) (k : Fin 3 × Fin 3 → ℂ) (i i' j : Fin 3) (q : R3) :
    (∑ a : Fin 3, ∑ b : Fin 3, eval k (act ν b a (X (i, b) * X (i', a) * realise j q))) =
      (∑ e : Fin 3, (ν e + (![1, 0, -1] : Fin 3 → ℂ) e) * (G k e i * G k e i')) *
          eval (fun a => k (a, j)) q
      + (∑ m : Fin 3, (if m < i then G k i m * G k m i' else if i < m then -(G k m m * G k i i') else 0)) *
          eval (fun a => k (a, j)) q
      + (∑ m : Fin 3, (if m < i' then G k i' i * G k m m else if i' < m then -(G k m i * G k i' m) else 0)) *
          eval (fun a => k (a, j)) q
      + ∑ l : Fin 3, (∑ m : Fin 3, (if m < l then G k l i * G k m i'
          else if l < m then -(G k m i * G k l i') else 0) * k (m, j)) *
          eval (fun a => k (a, j)) (pderiv l q) := by
  rw [Finset.sum_comm]; exact contr_AB ν k i i' j q

def rot (a : Fin 3) (q : R3) : R3 :=
  ∑ c : Fin 3, ∑ d : Fin 3,
    MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
      (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) * (MvPolynomial.X c * MvPolynomial.pderiv d q)

def lower1 (M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)) : MvPolynomial (Fin 3) ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
      (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
      (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))

def same2 (M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
    (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))

end

end WsB.C6

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open MvPolynomial

namespace WsB
namespace FT

open WsB.C6

theorem act_add (ν : Fin 3 → ℂ) (c d : Fin 3) (P Q : R9) : act ν c d (P + Q) = act ν c d P + act ν c d Q := by
  simp only [act, mul_add, map_add, Finset.sum_add_distrib]
  ring

theorem act_zero (ν : Fin 3 → ℂ) (c d : Fin 3) : act ν c d 0 = 0 := by
  simp [act]

theorem act_sum {ι : Type*} (ν : Fin 3 → ℂ) (c d : Fin 3) (s : Finset ι) (f : ι → R9) :
    act ν c d (∑ x ∈ s, f x) = ∑ x ∈ s, act ν c d (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [act_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, act_add, ih]

def detX : R9 := (Matrix.of fun i j : Fin 3 => (X (i, j) : R9)).det

def pt (o : Fin 3 → Fin 3 → ℝ) : Fin 3 × Fin 3 → ℂ := fun ij => ((o ij.1 ij.2 : ℝ) : ℂ)

def detC (o : Fin 3 → Fin 3 → ℝ) : ℂ := (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det

theorem eval_detX (o : Fin 3 → Fin 3 → ℝ) : eval (pt o) detX = detC o := by
  unfold detX detC
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [pt]

theorem act_detX_mul (ν : Fin 3 → ℂ) (c d : Fin 3) (P : R9) : act ν c d (detX * P) = detX * act ν c d P :=
  LanglandsTunnell.CubicInduction.inducedPicture_act_det_mul ν c d P

theorem act_detX_pow_mul (ν : Fin 3 → ℂ) (c d : Fin 3) (n : ℕ) (P : R9) :
    act ν c d (detX ^ n * P) = detX ^ n * act ν c d P := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_comm (detX ^ n) detX, mul_assoc, act_detX_mul, ih, ← mul_assoc]

theorem rowOrth_cast (o : Fin 3 → Fin 3 → ℝ)
    (ho : ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) (r s : Fin 3) :
    (∑ a : Fin 3, pt o (r, a) * pt o (s, a)) = if r = s then 1 else 0 := by
  have h1 : (Matrix.of o).transpose * Matrix.of o = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.transpose_apply] using ho i j
  have h2 : Matrix.of o * (Matrix.of o).transpose = 1 := mul_eq_one_comm.mp h1
  have h3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => ((M r s : ℝ) : ℂ)) h2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply] at h3
  push_cast at h3
  simp only [pt]
  rw [h3]
  split_ifs <;> simp

theorem pderiv_pderiv_eq_zero (p : R3) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) (hℓ : ℓ ≤ 1) (i j : Fin 3) :
    pderiv i (pderiv j p) = 0 := by
  have h1 : (pderiv j p).IsHomogeneous (ℓ - 1) := hp.pderiv
  have h0 : ℓ - 1 = 0 := by omega
  rw [h0] at h1
  have h2 := totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr h1)
  rw [h2, pderiv_C]

theorem lower2_Xi_eq_zero (ν : Fin 3 → ℂ) (p : R3) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) (hℓ : ℓ ≤ 1) :
    lower2 (Xi ν p) = 0 := by
  have h := pderiv_pderiv_eq_zero p ℓ hp hℓ
  rw [lower2_Xi]
  simp [h]

def Qab (p : R3) (a b : Fin 3) : R9 :=
  ∑ i : Fin 3, ∑ i' : Fin 3, X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))

theorem main
    (ν : Fin 3 → ℂ) (ε : Fin 3 → Fin 2) (Vε : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (hsm : ∀ G ∈ Vε, WhittakerBlock.IsArchSmooth3 G)
    (hB : ∀ G ∈ Vε, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g)
    (hstab : ∀ G ∈ Vε, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ Vε)
    (hflow : ∀ G ∈ Vε, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ Vε, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0)
    (S : ℕ)
    (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ Vε)
    (hread : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      detC o ^ ((ℓ + S) % 2) * eval (pt o) (realise 0 p) = G (WhittakerBlock.archRealLift3 o * k₁)) :
    ∃ G' ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      detC o ^ ((ℓ - 2 + S) % 2) * eval (pt o) (realise 0 (lower2 (Xi ν p))) =
        G' (WhittakerBlock.archRealLift3 o * k₁) := by
  classical
  set α : ℕ := (ℓ + S) % 2 with hα

  have hQT : ∀ a b : Fin 3, ∃ G' ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ,
      (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      detC o ^ α * eval (pt o) (Qab p a b) = G' (WhittakerBlock.archRealLift3 o * k₁) :=
    (LanglandsTunnell.CubicInduction.exists_mem_forall_det_pow_mul_eval_sum_quadric_mul_columnRealisation_eq
      Vε k₁ hk₁ hsm hstab hflow ℓ p hp 0 α G hG hread).1
  choose Gq hGqmem hGqread using hQT

  have hfl : ∀ a b c d : Fin 3, ∃ G' ∈ Vε, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasDerivAt (fun s : ℝ => Gq a b (g * WhittakerBlock.archRealLift3 fun a' b' =>
        (if a' = b' then (1 : ℝ) else 0) + if a' = c ∧ b' = d then s else 0)) (G' g) 0 :=
    fun a b c d => hflow (Gq a b) (hGqmem a b) c d
  choose Gf hGfmem hGfderiv using hfl

  have hGfval : ∀ a b c d : Fin 3, ∀ o : Fin 3 → Fin 3 → ℝ,
      (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      Gf a b c d (WhittakerBlock.archRealLift3 o * k₁) = eval (pt o) (act ν c d (detX ^ α * Qab p a b)) := by
    intro a b c d o ho
    have hP : ∀ o' : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o' a i * o' a j = if i = j then 1 else 0) →
        Gq a b (WhittakerBlock.archRealLift3 o' * k₁) = eval (pt o') (detX ^ α * Qab p a b) := by
      intro o' ho'
      rw [map_mul, map_pow, eval_detX]
      exact (hGqread a b o' ho').symm
    have h1 : HasDerivAt (fun s : ℝ => Gq a b (WhittakerBlock.archRealLift3 o * k₁ *
        WhittakerBlock.archRealLift3 fun a' b' => (if a' = b' then (1 : ℝ) else 0) + if a' = c ∧ b' = d then s else 0))
        (eval (pt o) (act ν c d (detX ^ α * Qab p a b))) 0 :=
      LanglandsTunnell.CubicInduction.hasDerivAt_archFlow_eq_eval_inducedPicture_act_of_upperTriangular_equivariant
        ν (Gq a b) (hB (Gq a b) (hGqmem a b)) k₁ hk₁ (detX ^ α * Qab p a b) hP o ho c d
    exact (hGfderiv a b c d (WhittakerBlock.archRealLift3 o * k₁)).unique h1

  have hproj : ∀ o : Fin 3 → Fin 3 → ℝ,
      (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (∑ a : Fin 3, ∑ b : Fin 3, (eval (pt o) (act ν a b (Qab p a b)) + eval (pt o) (act ν b a (Qab p a b)))) =
        eval (pt o) (realise 0 (lower2 (Xi ν p))) := by
    intro o ho
    have h6 : eval (pt o) (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
        C (1 / 2 : ℂ) * (act ν a b (X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))) +
          act ν b a (X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))))) =
        eval (pt o) (C (1 / 2 : ℂ) * realise 0 (lower2 (Xi ν p))) :=
      LanglandsTunnell.CubicInduction.eval_sum_act_quadric_realise_pderiv_pderiv_eq_half_eval_realise_lowerTwo
        ν 0 p hharm (pt o) (rowOrth_cast o ho)
    have h7 : (∑ a : Fin 3, ∑ b : Fin 3, (eval (pt o) (act ν a b (Qab p a b)) + eval (pt o) (act ν b a (Qab p a b)))) =
        2 * eval (pt o) (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
        C (1 / 2 : ℂ) * (act ν a b (X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))) +
          act ν b a (X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))))) := by
      have h22 : ∀ x : ℂ, (2 : ℂ) * (1 / 2 * x) = x := fun x => by ring
      simp only [Qab, act_sum, map_sum, map_add, map_mul, eval_C, Finset.mul_sum, h22]
      simp only [Finset.sum_add_distrib]
    rw [h7, h6, map_mul, eval_C]
    ring

  by_cases hℓ : 2 ≤ ℓ
  · have hpar : (ℓ - 2 + S) % 2 = α := by rw [hα]; omega
    refine ⟨∑ a : Fin 3, ∑ b : Fin 3, (Gf a b a b + Gf a b b a), ?_, ?_⟩
    · exact Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ =>
        Submodule.add_mem _ (hGfmem a b a b) (hGfmem a b b a)))
    · intro o ho
      rw [hpar]
      simp only [Finset.sum_apply, Pi.add_apply]
      simp only [hGfval _ _ _ _ o ho, act_detX_pow_mul, map_mul, map_pow, eval_detX]
      rw [← hproj o ho]
      simp only [Finset.mul_sum, mul_add]
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro o ho
    rw [lower2_Xi_eq_zero ν p ℓ hp (by omega), show realise 0 (0 : R3) = 0 from map_zero _]
    simp

end WsB.FT

end

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem solution
    (ν : Fin 3 → ℂ) (lam₁ lam₂ lam₃ : ℂ) (ε : Fin 3 → Fin 2) (V Vε : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (hVε : (∀ G ∈ Vε, Continuous G) ∧
      (∀ G ∈ Vε, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ Vε, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
      (∀ G ∈ Vε, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ Vε) ∧
      (∀ G ∈ Vε, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ G ∈ Vε, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ Vε, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0) ∧
      (∀ G ∈ Vε, ∀ σ : Fin 3 → Fin 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g) =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) * G g) ∧
      (∀ G ∈ Vε, ∃ F ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G g = (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)))
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0)
    (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ Vε)
    (hread : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
        G (WhittakerBlock.archRealLift3 o * k₁)) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    ∃ G' ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ - 2 + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (lower₂ (Ξ ν p))) =
        G' (WhittakerBlock.archRealLift3 o * k₁) :=
  WsB.FT.main ν ε Vε k₁ hk₁ (fun G hG => (hVε.2.1 G hG).1) hVε.2.2.1 hVε.2.2.2.1 hVε.2.2.2.2.2.1
    ℓ p hp hharm (∑ a : Fin 3, (ε a : ℕ)) G hG hread

end S_LanglandsTunnell_CubicInduction_exists_read_lowerTwo_xi_of_read_signIsotypic
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_read_lowerTwo_xi_of_read_signIsotypic (solution)
