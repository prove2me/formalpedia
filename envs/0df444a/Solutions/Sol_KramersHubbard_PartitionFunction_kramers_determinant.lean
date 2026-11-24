-- Prove2me | solution 1 for KramersHubbard.PartitionFunction.kramers_determinant
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:52:36.174985+00:00
-- url     : https://prove2.me/submissions/1500f853-895b-444d-bee3-b050ba0fb257

import Definitions.Def_KramersHubbard_PartitionFunction_Quaternion

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory KramersHubbard.PartitionFunction

namespace KramersAux

def eqv (n : ℕ) : Fin 2 ⊕ (Fin n × Fin 2) ≃ Fin (n + 1) × Fin 2 where
  toFun := Sum.elim (fun a => (0, a)) (fun x => (x.1.succ, x.2))
  invFun := fun x => if h : x.1 = 0 then Sum.inl x.2 else Sum.inr (x.1.pred h, x.2)
  left_inv := by
    rintro (a | ⟨i, a⟩)
    · simp
    · simp [Fin.succ_ne_zero]
  right_inv := by
    rintro ⟨i, a⟩
    by_cases h : i = 0
    · subst h; simp
    · simp [h]

lemma pivot (n : ℕ)
    (IH : ∀ S : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ, Quaternionic S →
      ∃ d : ℝ, 0 ≤ d ∧ S.det = d)
    (Q : Matrix (Fin (n + 1) × Fin 2) (Fin (n + 1) × Fin 2) ℂ) (hQ : Quaternionic Q)
    (hp : Q (0, 0) (0, 0) ≠ 0 ∨ Q (0, 1) (0, 0) ≠ 0) :
    ∃ d : ℝ, 0 ≤ d ∧ Q.det = d := by
  have h1 : ∀ a b, Q (a, 0) (b, 1) = -star (Q (a, 1) (b, 0)) := fun a b => (hQ a b).1
  have h2 : ∀ a b, Q (a, 1) (b, 1) = star (Q (a, 0) (b, 0)) := fun a b => (hQ a b).2
  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    Q.submatrix (fun a => ((0 : Fin (n + 1)), a)) (fun b => ((0 : Fin (n + 1)), b)) with hA
  set B : Matrix (Fin 2) (Fin n × Fin 2) ℂ :=
    Q.submatrix (fun a => ((0 : Fin (n + 1)), a)) (fun y => (y.1.succ, y.2)) with hB
  set C : Matrix (Fin n × Fin 2) (Fin 2) ℂ :=
    Q.submatrix (fun x => (x.1.succ, x.2)) (fun b => ((0 : Fin (n + 1)), b)) with hC
  set D : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
    Q.submatrix (fun x => (x.1.succ, x.2)) (fun y => (y.1.succ, y.2)) with hD
  have hblk : Q.submatrix (eqv n) (eqv n) = Matrix.fromBlocks A B C D := by
    ext x y
    rcases x with a | ⟨i, a⟩ <;> rcases y with b | ⟨j, b⟩ <;> rfl
  have hdetA : A.det =
      ((Complex.normSq (Q (0, 0) (0, 0)) + Complex.normSq (Q (0, 1) (0, 0)) : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two]
    simp only [hA, Matrix.submatrix_apply, h1, h2]
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have hpos : 0 < Complex.normSq (Q (0, 0) (0, 0)) + Complex.normSq (Q (0, 1) (0, 0)) := by
    have := Complex.normSq_nonneg (Q (0, 0) (0, 0))
    have := Complex.normSq_nonneg (Q (0, 1) (0, 0))
    rcases hp with h | h
    · have := Complex.normSq_pos.mpr h; linarith
    · have := Complex.normSq_pos.mpr h; linarith
  have hAu : IsUnit A.det := by
    rw [hdetA]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hpos.ne')
  letI := Matrix.invertibleOfIsUnitDet A hAu
  set S := D - C * A⁻¹ * B with hS
  have i00 : A⁻¹ 0 0 = (A 0 0 * A 1 1 - A 0 1 * A 1 0)⁻¹ * A 1 1 := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.det_fin_two, Matrix.adjugate_fin_two]; simp
  have i01 : A⁻¹ 0 1 = (A 0 0 * A 1 1 - A 0 1 * A 1 0)⁻¹ * -A 0 1 := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.det_fin_two, Matrix.adjugate_fin_two]; simp
  have i10 : A⁻¹ 1 0 = (A 0 0 * A 1 1 - A 0 1 * A 1 0)⁻¹ * -A 1 0 := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.det_fin_two, Matrix.adjugate_fin_two]; simp
  have i11 : A⁻¹ 1 1 = (A 0 0 * A 1 1 - A 0 1 * A 1 0)⁻¹ * A 0 0 := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.det_fin_two, Matrix.adjugate_fin_two]; simp
  have hSq : Quaternionic S := by
    intro i j
    simp only [hS, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, i00, i01, i10, i11]
    simp only [hA, hB, hC, hD, Matrix.submatrix_apply, h1, h2]
    constructor
    · simp only [star_sub, star_add, star_mul', star_neg, star_star, star_inv₀]
      ring
    · simp only [star_sub, star_add, star_mul', star_neg, star_star, star_inv₀]
      ring
  obtain ⟨d, hd0, hd⟩ := IH S hSq
  refine ⟨(Complex.normSq (Q (0, 0) (0, 0)) + Complex.normSq (Q (0, 1) (0, 0))) * d,
    mul_nonneg hpos.le hd0, ?_⟩
  rw [← Matrix.det_submatrix_equiv_self (eqv n) Q, hblk, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, ← hS, hd, hdetA]
  push_cast
  ring

theorem main : ∀ (n : ℕ) (Q : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ), Quaternionic Q →
    ∃ d : ℝ, 0 ≤ d ∧ Q.det = d := by
  intro n
  induction n with
  | zero =>
    intro Q _
    exact ⟨1, zero_le_one, by rw [Matrix.det_isEmpty]; simp⟩
  | succ n ih =>
    intro Q hQ
    by_cases hz : ∃ r : Fin (n + 1), Q (r, 0) (0, 0) ≠ 0 ∨ Q (r, 1) (0, 0) ≠ 0
    · obtain ⟨r, hr⟩ := hz
      set Q' := Q.submatrix (Equiv.prodCongrLeft fun _ : Fin 2 => Equiv.swap (0 : Fin (n + 1)) r) id
        with hQ'
      have hQ'q : Quaternionic Q' := fun i j => hQ (Equiv.swap (0 : Fin (n + 1)) r i) j
      have hp : Q' (0, 0) (0, 0) ≠ 0 ∨ Q' (0, 1) (0, 0) ≠ 0 := by
        change Q (Equiv.swap (0 : Fin (n + 1)) r 0, 0) (0, 0) ≠ 0 ∨
          Q (Equiv.swap (0 : Fin (n + 1)) r 0, 1) (0, 0) ≠ 0
        rw [Equiv.swap_apply_left]
        exact hr
      obtain ⟨d, hd0, hd⟩ := pivot n ih Q' hQ'q hp
      refine ⟨d, hd0, ?_⟩
      rw [← hd, hQ']
      simp [Matrix.det_permute, Equiv.Perm.sign_prodCongrLeft]
    · push_neg at hz
      refine ⟨0, le_refl _, ?_⟩
      rw [Matrix.det_eq_zero_of_column_eq_zero ((0 : Fin (n + 1)), (0 : Fin 2)) ?_]
      · simp
      · rintro ⟨r, a⟩
        fin_cases a
        · exact (hz r).1
        · exact (hz r).2

end KramersAux

theorem solution {p : ℕ}
    (Q : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ) (hQ : Quaternionic Q) :
    ∃ d : ℝ, 0 ≤ d ∧ Q.det = (d : ℂ) :=
  KramersAux.main p Q hQ
