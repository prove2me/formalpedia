-- Prove2me | solution 1 for MTT.Cohomology.manin_generation
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T15:38:55.318321+00:00
-- url     : https://prove2.me/submissions/64b4e938-c84d-4864-832b-4817742440ec

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
open MTT.Cohomology

namespace P2MMG

open MvPolynomial

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-! ### The action of `SL(2,ℤ)` on the cusps, in coordinates -/

theorem cuspAct_infty (g : SL2) :
    cuspAct g OnePoint.infty
      = if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 then OnePoint.infty
        else ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ)
              / ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_infty_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem cuspAct_zero (g : SL2) :
    cuspAct g ((0 : ℚ) : Cusp)
      = if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 then OnePoint.infty
        else ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℚ)
              / ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_some_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem cuspAct_mul (g h : SL2) (x : Cusp) :
    cuspAct (g * h) x = cuspAct g (cuspAct h x) := by
  simp [cuspAct, map_mul, mul_smul]

/-! ### Elementary consequences of the cocycle relation -/

variable {N n : ℕ} {R : Type*} [CommRing R]

theorem hc_add (φ : Hc N n R) (x y z : Cusp) :
    φ.val (x, y) + φ.val (y, z) = φ.val (x, z) := φ.2.2.1 x y z

theorem hc_hom (φ : Hc N n R) (x y : Cusp) : φ.val (x, y) ∈ MTT.Cohomology.Sym R n := φ.2.1 x y

theorem hc_equiv (φ : Hc N n R) (γ : CongruenceSubgroup.Gamma1 N) (x y : Cusp) :
    φ.val (cuspAct γ.val x, cuspAct γ.val y) = act γ.val.val (φ.val (x, y)) :=
  φ.2.2.2 γ x y

theorem hc_self (φ : Hc N n R) (x : Cusp) : φ.val (x, x) = 0 := by
  have h := hc_add φ x x x
  have h2 : φ.val (x, x) + φ.val (x, x) = 0 + φ.val (x, x) := by rw [zero_add]; exact h
  exact add_right_cancel h2

theorem hc_swap (φ : Hc N n R) (x y : Cusp) : φ.val (y, x) = -φ.val (x, y) := by
  have h : φ.val (x, y) + φ.val (y, x) = 0 := by rw [hc_add φ x y x, hc_self]
  have h2 : φ.val (x, y) + φ.val (y, x) - φ.val (x, y) = 0 - φ.val (x, y) := by rw [h]
  simpa [add_sub_cancel_left] using h2

end P2MMG

namespace P2MMG

open MvPolynomial

variable {N n : ℕ} {R : Type*} [CommRing R]

/-- Manin's trick. If `φ` kills every unimodular path `(g·0, g·∞)`, it kills every
path `(∞, p/q)`; the induction is on the denominator. -/
theorem manin_aux (φ : Hc N n R)
    (hU : ∀ g : SL2, φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    ∀ (m : ℕ) (p q : ℤ), 0 < q → q ≤ (m : ℤ) → IsCoprime p q →
      φ.val (OnePoint.infty, (((p : ℚ) / (q : ℚ)) : Cusp)) = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p q hq hqm hcop
    obtain ⟨u, v, huv⟩ := hcop
    set q' : ℤ := u % q with hq'def
    set p' : ℤ := -(v + p * (u / q)) with hp'def
    have hdet : p * q' - p' * q = 1 := by
      rw [hq'def, hp'def, Int.emod_def]
      linear_combination huv
    have hMdet : (!![p, p'; q, q'] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
      rw [Matrix.det_fin_two_of]; exact hdet
    set g : SL2 := ⟨!![p, p'; q, q'], hMdet⟩ with hgdef
    have hg00 : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by simp [hgdef]
    have hg01 : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = p' := by simp [hgdef]
    have hg10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = q := by simp [hgdef]
    have hg11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = q' := by simp [hgdef]
    have hU' := hU g
    rw [cuspAct_infty, hg10, hg00, if_neg hq.ne', cuspAct_zero, hg11, hg01] at hU'
    by_cases hq'0 : q' = 0
    · rw [if_pos hq'0] at hU'
      exact hU'
    · rw [if_neg hq'0] at hU'
      have hq'pos : 0 < q' := lt_of_le_of_ne (Int.emod_nonneg u hq.ne') (Ne.symm hq'0)
      have hq'lt : q' < q := Int.emod_lt_of_pos u hq
      have hcop' : IsCoprime p' q' := ⟨-q, p, by linear_combination hdet⟩
      have hrec : φ.val (OnePoint.infty, (((p' : ℚ) / (q' : ℚ)) : Cusp)) = 0 := by
        refine ih q'.toNat (by omega) p' q' hq'pos ?_ hcop'
        omega
      have hsum := hc_add φ OnePoint.infty (((p' : ℚ) / (q' : ℚ)) : Cusp)
        (((p : ℚ) / (q : ℚ)) : Cusp)
      rw [hrec, hU', zero_add] at hsum
      exact hsum.symm

theorem manin (φ : Hc N n R)
    (hU : ∀ g : SL2, φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0)
    (r : ℚ) : φ.val (OnePoint.infty, (r : Cusp)) = 0 := by
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using r.reduced
  have h := manin_aux φ hU r.den r.num (r.den : ℤ)
    (by exact_mod_cast r.pos) le_rfl hcop
  have hcast : (((r.den : ℤ) : ℚ)) = (r.den : ℚ) := by push_cast; ring
  rw [hcast, Rat.num_div_den] at h
  exact h

/-- A class killed on all unimodular paths is zero. -/
theorem hc_eq_zero_of_unimodular (φ : Hc N n R)
    (hU : ∀ g : SL2, φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    φ = 0 := by
  have hinf : ∀ x : Cusp, φ.val (OnePoint.infty, x) = 0 := by
    intro x
    induction x using OnePoint.rec with
    | infty => exact hc_self φ _
    | coe r => exact manin φ hU r
  refine Subtype.ext (funext fun D => ?_)
  have hsum := hc_add φ D.1 OnePoint.infty D.2
  rw [hinf D.2, add_zero] at hsum
  have : φ.val (D.1, OnePoint.infty) = 0 := by
    rw [hc_swap φ OnePoint.infty D.1, hinf D.1, neg_zero]
  rw [this] at hsum
  simpa using hsum.symm

end P2MMG


open P2MMG in
/-- Manin: the unimodular paths generate `Div⁰(P¹(ℚ))`, so a class killing all of them is zero. -/
theorem solution {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R)
    (hU : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    φ = 0 :=
  hc_eq_zero_of_unimodular φ hU
