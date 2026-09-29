-- Prove2me | solution 1 for Matrix.exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/613b2a89-5f27-5347-a54d-5a02c203b1e5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace P2mWhitehead

open Matrix

section Ring

variable {A : Type*} [Ring A]

def E (p : Bool × A) : Matrix (Fin 2) (Fin 2) A :=
  if p.1 then !![(1 : A), p.2; 0, 1] else !![(1 : A), 0; p.2, 1]

def W (l : List (Bool × A)) : Matrix (Fin 2) (Fin 2) A := (l.map E).prod

theorem W_def (l : List (Bool × A)) :
    W l = (l.map fun p : Bool × A => if p.1 then !![(1 : A), p.2; 0, 1] else !![(1 : A), 0; p.2, 1]).prod :=
  rfl

@[scoped simp] theorem W_nil : W ([] : List (Bool × A)) = 1 := by simp [W]

@[scoped simp] theorem W_cons (p : Bool × A) (l : List (Bool × A)) : W (p :: l) = E p * W l := by
  simp [W]

theorem W_append (l l' : List (Bool × A)) : W (l ++ l') = W l * W l' := by
  simp [W, List.map_append, List.prod_append]

@[scoped simp] theorem E_true (t : A) : E (true, t) = !![(1 : A), t; 0, 1] := rfl
@[scoped simp] theorem E_false (t : A) : E (false, t) = !![(1 : A), 0; t, 1] := rfl

theorem fin_two_eq {a b c d a' b' c' d' : A} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c') (h₄ : d = d') :
    !![a, b; c, d] = !![a', b'; c', d'] := by
  subst h₁ h₂ h₃ h₄; rfl

theorem upper_mul (t a b c d : A) :
    !![(1 : A), t; 0, 1] * !![a, b; c, d] = !![a + t * c, b + t * d; c, d] := by
  rw [Matrix.mul_fin_two]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

theorem lower_mul (t a b c d : A) :
    !![(1 : A), 0; t, 1] * !![a, b; c, d] = !![a, b; t * a + c, t * b + d] := by
  rw [Matrix.mul_fin_two]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

theorem one_eq : (1 : Matrix (Fin 2) (Fin 2) A) = !![(1 : A), 0; 0, 1] := Matrix.one_fin_two

theorem diag_mul_diag (x y : A) :
    !![(1 : A), 0; 0, x] * !![(1 : A), 0; 0, y] = !![(1 : A), 0; 0, x * y] := by
  rw [Matrix.mul_fin_two]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

theorem W_commutator (P Q : A) (h : Q * P = 0) :
    W [(false, P), (true, Q), (false, -P), (true, -Q)] = !![(1 : A), 0; 0, 1 + P * Q] := by
  have hx : ∀ x : A, Q * (P * x) = 0 := fun x => by rw [← mul_assoc, h, zero_mul]
  simp only [W_cons, W_nil, E_true, E_false, one_eq, upper_mul, lower_mul]
  refine fin_two_eq ?_ ?_ ?_ ?_ <;> simp [mul_add, add_mul, mul_assoc, h, hx]
  abel

theorem W_weyl : W [(true, (1 : A)), (false, -1), (true, 1)] = !![(0 : A), 1; -1, 0] := by
  simp only [W_cons, W_nil, E_true, E_false, one_eq, upper_mul, lower_mul]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

theorem W_weyl_inv : W [(true, (-1 : A)), (false, 1), (true, -1)] = !![(0 : A), -1; 1, 0] := by
  simp only [W_cons, W_nil, E_true, E_false, one_eq, upper_mul, lower_mul]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

theorem W_conj_diag (l : List (Bool × A)) (s : A) (hl : W l = !![(1 : A), 0; 0, s]) :
    W ([(true, (1 : A)), (false, -1), (true, 1)] ++ l ++ [(true, (-1 : A)), (false, 1), (true, -1)]) =
      !![s, 0; 0, 1] := by
  rw [W_append, W_append, W_weyl, hl, W_weyl_inv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

theorem W_diag_mul {l l' : List (Bool × A)} {x y : A} (hl : W l = !![(1 : A), 0; 0, x])
    (hl' : W l' = !![(1 : A), 0; 0, y]) : W (l ++ l') = !![(1 : A), 0; 0, x * y] := by
  rw [W_append, hl, hl', diag_mul_diag]

theorem W_whitehead (u : Aˣ) :
    W [(true, ((u⁻¹ : Aˣ) : A)), (false, -(u : A)), (true, ((u⁻¹ : Aˣ) : A)),
      (true, (-1 : A)), (false, 1), (true, -1)] = !![((u⁻¹ : Aˣ) : A), 0; 0, (u : A)] := by
  simp only [W_cons, W_nil, E_true, E_false, one_eq, upper_mul, lower_mul]
  refine fin_two_eq ?_ ?_ ?_ ?_ <;> simp [mul_add, add_mul, mul_assoc]

theorem diag_units_eq (g₁ g₂ : Aˣ) :
    (!![(g₁ : A), 0; 0, (g₂ : A)] : Matrix (Fin 2) (Fin 2) A) =
      !![(g₁ : A) * g₂, 0; 0, 1] * !![((g₂⁻¹ : Aˣ) : A), 0; 0, (g₂ : A)] := by
  rw [Matrix.mul_fin_two]
  refine fin_two_eq ?_ ?_ ?_ ?_ <;> simp [mul_assoc]

theorem map_W {B : Type*} [Ring B] (f : A →+* B) (l : List (Bool × A)) :
    f.mapMatrix (W l) = W (l.map fun p => (p.1, f p.2)) := by
  induction l with
  | nil => simp [W]
  | cons p l ih =>
    rw [W_cons, map_mul, ih, List.map_cons, W_cons]
    congr 1
    rcases p with ⟨b, t⟩
    cases b
    · simp only [E_false]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    · simp only [E_true]
      ext i j; fin_cases i <;> fin_cases j <;> simp

end Ring

section Field

variable {F : Type*} [Field F]

theorem exists_W_eq_diag_upper (t : F) :
    ∃ l : List (Bool × Matrix (Fin 2) (Fin 2) F),
      W l = !![(1 : Matrix (Fin 2) (Fin 2) F), 0; 0, !![1, t; 0, 1]] := by
  refine ⟨[(false, !![t, 0; 0, 0]), (true, !![0, 1; 0, 0]), (false, -!![t, 0; 0, 0]),
    (true, -!![0, 1; 0, 0])], ?_⟩
  rw [W_commutator]
  · refine fin_two_eq rfl rfl rfl ?_
    rw [one_eq, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_W_eq_diag_lower (t : F) :
    ∃ l : List (Bool × Matrix (Fin 2) (Fin 2) F),
      W l = !![(1 : Matrix (Fin 2) (Fin 2) F), 0; 0, !![1, 0; t, 1]] := by
  refine ⟨[(false, !![0, 0; t, 0]), (true, !![1, 0; 0, 0]), (false, -!![0, 0; t, 0]),
    (true, -!![1, 0; 0, 0])], ?_⟩
  rw [W_commutator]
  · refine fin_two_eq rfl rfl rfl ?_
    rw [one_eq, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_eq_prod_of_det_eq_one' (a b c d : F) (h : a * d - b * c = 1) :
    ∃ e x y z : F, (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; -e, 1] * !![1, x; 0, 1] * !![1, 0; y, 1] * !![1, z; 0, 1] := by
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by rw [mul_zero, sub_zero] at h; exact h
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    refine ⟨1, (a - 1) / a, a, (b + d - 1) / a, ?_⟩
    simp only [Matrix.mul_fin_two]
    refine fin_two_eq ?_ ?_ ?_ ?_
    · field_simp; ring
    · field_simp; linear_combination -had
    · field_simp; ring
    · field_simp; linear_combination had
  · refine ⟨0, (a - 1) / c, c, (d - 1) / c, ?_⟩
    simp only [Matrix.mul_fin_two]
    refine fin_two_eq ?_ ?_ ?_ ?_
    · field_simp; ring
    · field_simp; linear_combination -h
    · simp
    · field_simp; ring

theorem exists_eq_prod_of_det_eq_one (s : Matrix (Fin 2) (Fin 2) F) (hs : s.det = 1) :
    ∃ e x y z : F, s = !![1, 0; -e, 1] * !![1, x; 0, 1] * !![1, 0; y, 1] * !![1, z; 0, 1] := by
  rw [Matrix.det_fin_two] at hs
  rw [Matrix.eta_fin_two s]
  exact exists_eq_prod_of_det_eq_one' _ _ _ _ hs

theorem exists_W_eq_diag_of_det_eq_one (s : Matrix (Fin 2) (Fin 2) F) (hs : s.det = 1) :
    ∃ l : List (Bool × Matrix (Fin 2) (Fin 2) F),
      W l = !![(1 : Matrix (Fin 2) (Fin 2) F), 0; 0, s] := by
  obtain ⟨e, x, y, z, rfl⟩ := exists_eq_prod_of_det_eq_one s hs
  obtain ⟨l₁, h₁⟩ := exists_W_eq_diag_lower (F := F) (-e)
  obtain ⟨l₂, h₂⟩ := exists_W_eq_diag_upper (F := F) x
  obtain ⟨l₃, h₃⟩ := exists_W_eq_diag_lower (F := F) y
  obtain ⟨l₄, h₄⟩ := exists_W_eq_diag_upper (F := F) z
  exact ⟨_, W_diag_mul (W_diag_mul (W_diag_mul h₁ h₂) h₃) h₄⟩

end Field

theorem exists_W_eq_diag {A : Type*} [Ring A] {F : Type*} [Field F]
    (φ : A ≃+* Matrix (Fin 2) (Fin 2) F) (s : A) (hs : (φ s).det = 1) :
    ∃ l : List (Bool × A), W l = !![(1 : A), 0; 0, s] := by
  obtain ⟨l, hl⟩ := exists_W_eq_diag_of_det_eq_one (φ s) hs
  refine ⟨l.map fun p => (p.1, φ.symm p.2), ?_⟩
  have := map_W (φ.symm : Matrix (Fin 2) (Fin 2) F →+* A) l
  simp only [RingHom.coe_coe] at this
  rw [← this, hl]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end P2mWhitehead
p2m_reactivate "P2MW.S_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one.P2mWhitehead"

open P2mWhitehead in
theorem solution
    {A : Type*} [Ring A] {F : Type*} [Field F]
    (φ : A ≃+* Matrix (Fin 2) (Fin 2) F) (g₁ g₂ : Aˣ) (h : (φ ((g₁ : A) * g₂)).det = 1) :
    ∃ l : List (Bool × A),
      (l.map fun p : Bool × A =>
        if p.1 then !![(1 : A), p.2; 0, 1] else !![(1 : A), 0; p.2, 1]).prod = !![(g₁ : A), 0; 0, (g₂ : A)] := by
  obtain ⟨l, hl⟩ := exists_W_eq_diag φ ((g₁ : A) * g₂) h
  refine ⟨([(true, (1 : A)), (false, -1), (true, 1)] ++ l ++ [(true, (-1 : A)), (false, 1), (true, -1)]) ++
    [(true, ((g₂⁻¹ : Aˣ) : A)), (false, -(g₂ : A)), (true, ((g₂⁻¹ : Aˣ) : A)),
      (true, (-1 : A)), (false, 1), (true, -1)], ?_⟩
  rw [diag_units_eq g₁ g₂]
  change W _ = _
  rw [W_append, W_conj_diag l _ hl, W_whitehead]

end S_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one
end P2MW
export P2MW.S_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one (solution)
