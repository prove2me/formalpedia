-- Prove2me | solution 1 for LinearOptimization.lp_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T21:10:25.716846+00:00
-- url     : https://prove2.me/submissions/8075fdfb-7429-4edb-83ff-80c055c24dae

import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype
import Theorems.Thm_LinearOptimization_lp_weak_duality
import Theorems.Thm_LinearOptimization_lp_optimal_certificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

open Matrix

theorem solution
    {m n : ℕ} (P : LinearOptimization.GeneralFormLP m n)
    (x : Fin n → ℝ)
    (hx : LinearOptimization.IsLpOptimal P.c
      (LinearOptimization.generalFeasibleSet P) x) :
    ∃ p : Fin m → ℝ,
      LinearOptimization.IsLpDualOptimal P.b
        (LinearOptimization.generalFeasibleSet (LinearOptimization.dualLP P)) p ∧
      p ⬝ᵥ P.b = P.c ⬝ᵥ x := by
  classical
  let B : Matrix ((Fin m × Bool) ⊕ (Fin n × Bool)) (Fin n) ℝ := fun r ↦
    match r with
    | Sum.inl (i, false) =>
        match P.rowRel i with
        | .ge => -P.A i
        | .le => 0
        | .eq => -P.A i
    | Sum.inl (i, true) =>
        match P.rowRel i with
        | .ge => 0
        | .le => P.A i
        | .eq => P.A i
    | Sum.inr (j, false) =>
        match P.colSign j with
        | .nonneg => -Pi.single j 1
        | .nonpos => 0
        | .free => 0
    | Sum.inr (j, true) =>
        match P.colSign j with
        | .nonneg => 0
        | .nonpos => Pi.single j 1
        | .free => 0
  let rhs : ((Fin m × Bool) ⊕ (Fin n × Bool)) → ℝ := fun r ↦
    match r with
    | Sum.inl (i, false) =>
        match P.rowRel i with
        | .ge => -P.b i
        | .le => 0
        | .eq => -P.b i
    | Sum.inl (i, true) =>
        match P.rowRel i with
        | .ge => 0
        | .le => P.b i
        | .eq => P.b i
    | Sum.inr _ => 0
  have hsystem (y : Fin n → ℝ) :
      B.mulVec y ≤ rhs ↔ y ∈ LinearOptimization.generalFeasibleSet P := by
    constructor
    · intro h
      constructor
      · intro i
        cases hrel : P.rowRel i with
        | ge =>
            have hi := h (Sum.inl (i, false))
            simpa [B, rhs, Matrix.mulVec, dotProduct, hrel,
              LinearOptimization.LinearConstraint.IsSatisfiedAt] using hi
        | le =>
            have hi := h (Sum.inl (i, true))
            simpa [B, rhs, Matrix.mulVec, dotProduct, hrel,
              LinearOptimization.LinearConstraint.IsSatisfiedAt] using hi
        | eq =>
            have hi₁ := h (Sum.inl (i, false))
            have hi₂ := h (Sum.inl (i, true))
            simp [B, rhs, Matrix.mulVec, dotProduct, hrel] at hi₁ hi₂
            simpa [LinearOptimization.LinearConstraint.IsSatisfiedAt, hrel, dotProduct] using
              le_antisymm hi₂ hi₁
      · intro j
        cases hsign : P.colSign j with
        | nonneg =>
            have hj := h (Sum.inr (j, false))
            simpa [B, rhs, Matrix.mulVec, dotProduct, Pi.single_apply, hsign,
              LinearOptimization.VarSign.IsSatisfiedBy] using hj
        | nonpos =>
            have hj := h (Sum.inr (j, true))
            simpa [B, rhs, Matrix.mulVec, dotProduct, Pi.single_apply, hsign,
              LinearOptimization.VarSign.IsSatisfiedBy] using hj
        | free => simp [LinearOptimization.VarSign.IsSatisfiedBy]
    · rintro ⟨hrow, hsign⟩ r
      rcases r with ⟨i, s⟩ | ⟨j, s⟩
      · cases s with
        | false =>
            cases hrel : P.rowRel i with
            | ge =>
                simpa [B, rhs, Matrix.mulVec, dotProduct, hrel,
                  LinearOptimization.LinearConstraint.IsSatisfiedAt] using hrow i
            | le => simp [B, rhs, Matrix.mulVec, dotProduct, hrel]
            | eq =>
                have hi := hrow i
                simp [LinearOptimization.LinearConstraint.IsSatisfiedAt, hrel, dotProduct] at hi
                simp [B, rhs, Matrix.mulVec, dotProduct, hrel]
                linarith
        | true =>
            cases hrel : P.rowRel i with
            | ge => simp [B, rhs, Matrix.mulVec, dotProduct, hrel]
            | le =>
                simpa [B, rhs, Matrix.mulVec, dotProduct, hrel,
                  LinearOptimization.LinearConstraint.IsSatisfiedAt] using hrow i
            | eq =>
                have hi := hrow i
                simp [LinearOptimization.LinearConstraint.IsSatisfiedAt, hrel] at hi
                simpa [B, rhs, Matrix.mulVec, dotProduct, hrel,
                  LinearOptimization.LinearConstraint.IsSatisfiedAt] using le_of_eq hi
      · cases s with
        | false =>
            cases hcol : P.colSign j with
            | nonneg =>
                simpa [B, rhs, Matrix.mulVec, dotProduct, Pi.single_apply, hcol,
                  LinearOptimization.VarSign.IsSatisfiedBy] using hsign j
            | nonpos => simp [B, rhs, Matrix.mulVec, dotProduct, hcol]
            | free => simp [B, rhs, Matrix.mulVec, dotProduct, hcol]
        | true =>
            cases hcol : P.colSign j with
            | nonneg => simp [B, rhs, Matrix.mulVec, dotProduct, hcol]
            | nonpos =>
                simpa [B, rhs, Matrix.mulVec, dotProduct, Pi.single_apply, hcol,
                  LinearOptimization.VarSign.IsSatisfiedBy] using hsign j
            | free => simp [B, rhs, Matrix.mulVec, dotProduct, hcol]
  have hfeas : ∃ y : Fin n → ℝ, B.mulVec y ≤ rhs :=
    ⟨x, (hsystem x).2 hx.1⟩
  have hvalid : ∀ y : Fin n → ℝ, B.mulVec y ≤ rhs →
      (-P.c) ⬝ᵥ y ≤ -(P.c ⬝ᵥ x) := by
    intro y hy
    have hopt := hx.2 y ((hsystem y).1 hy)
    simpa [dotProduct] using neg_le_neg hopt
  obtain ⟨lam, hlam, hstat, hobj⟩ :=
    (LinearOptimization.farkas_inequality_form_fintype
      B rhs (-P.c) (-(P.c ⬝ᵥ x)) hfeas).mp hvalid
  let p : Fin m → ℝ := fun i ↦
    match P.rowRel i with
    | .ge => lam (Sum.inl (i, false))
    | .le => -lam (Sum.inl (i, true))
    | .eq => lam (Sum.inl (i, false)) - lam (Sum.inl (i, true))
  let slack : Fin n → ℝ := fun j ↦
    match P.colSign j with
    | .nonneg => -lam (Sum.inr (j, false))
    | .nonpos => lam (Sum.inr (j, true))
    | .free => 0
  have hrows (j : Fin n) :
      (∑ r : Fin m × Bool, B (Sum.inl r) j * lam (Sum.inl r)) =
        -(p ⬝ᵥ (fun i ↦ P.A i j)) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [dotProduct, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases hrel : P.rowRel i <;> simp [B, p, hrel] <;> ring
  have hvars (j : Fin n) :
      (∑ r : Fin n × Bool, B (Sum.inr r) j * lam (Sum.inr r)) = slack j := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [Finset.sum_eq_single j]
    · cases hsign : P.colSign j <;> simp [B, slack, hsign, Pi.single_apply]
    · intro i _ hij
      cases hsign : P.colSign i <;>
        simp [B, hsign, Pi.single_apply, hij, Ne.symm hij]
    · simp
  have hstationary (j : Fin n) :
      -(p ⬝ᵥ (fun i ↦ P.A i j)) + slack j = -P.c j := by
    have hj := congrFun hstat j
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Matrix.transpose_apply] at hj
    rw [Fintype.sum_sum_type, hrows j, hvars j] at hj
    exact hj
  have hpfeas : p ∈ LinearOptimization.generalFeasibleSet
      (LinearOptimization.dualLP P) := by
    constructor
    · intro j
      have hs := hstationary j
      have hneg : (-P.Aᵀ) j ⬝ᵥ p =
          -(p ⬝ᵥ (fun i ↦ P.A i j)) := by
        simp [dotProduct, mul_comm]
      cases hsign : P.colSign j with
      | nonneg =>
          have hlam₀ : 0 ≤ lam (Sum.inr (j, false)) := hlam _
          simp [slack, hsign] at hs
          simp [LinearOptimization.dualLP, LinearOptimization.VarSign.dualRel,
            LinearOptimization.LinearConstraint.IsSatisfiedAt, hsign, hneg]
          linarith
      | nonpos =>
          have hlam₀ : 0 ≤ lam (Sum.inr (j, true)) := hlam _
          simp [slack, hsign] at hs
          simp [LinearOptimization.dualLP, LinearOptimization.VarSign.dualRel,
            LinearOptimization.LinearConstraint.IsSatisfiedAt, hsign, hneg]
          linarith
      | free =>
          simp [slack, hsign] at hs
          simp [LinearOptimization.dualLP, LinearOptimization.VarSign.dualRel,
            LinearOptimization.LinearConstraint.IsSatisfiedAt, hsign, hneg]
          linarith
    · intro i
      cases hrel : P.rowRel i with
      | ge =>
          simpa [LinearOptimization.dualLP, LinearOptimization.ConstraintRel.dualSign,
            LinearOptimization.VarSign.IsSatisfiedBy, p, hrel] using
            (hlam (Sum.inl (i, false)))
      | le =>
          simpa [LinearOptimization.dualLP, LinearOptimization.ConstraintRel.dualSign,
            LinearOptimization.VarSign.IsSatisfiedBy, p, hrel] using
            (neg_nonpos.mpr (hlam (Sum.inl (i, true))))
      | eq =>
          simp [LinearOptimization.dualLP, LinearOptimization.ConstraintRel.dualSign,
            LinearOptimization.VarSign.IsSatisfiedBy, hrel]
  have hrowsObj :
      (∑ r : Fin m × Bool, lam (Sum.inl r) * rhs (Sum.inl r)) =
        -(p ⬝ᵥ P.b) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [dotProduct, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases hrel : P.rowRel i <;> simp [rhs, p, hrel] <;> ring
  have hobj' : -(p ⬝ᵥ P.b) ≤ -(P.c ⬝ᵥ x) := by
    have := hobj
    simp only [dotProduct] at this
    rw [Fintype.sum_sum_type] at this
    rw [show (∑ r : Fin n × Bool, lam (Sum.inr r) * rhs (Sum.inr r)) = 0 by
      simp [rhs]] at this
    rw [hrowsObj] at this
    simpa [dotProduct] using this
  have hweak := LinearOptimization.lp_weak_duality P x hx.1 p hpfeas
  have heq : p ⬝ᵥ P.b = P.c ⬝ᵥ x := by
    linarith
  have hcert := LinearOptimization.lp_optimal_certificate P x hx.1 p hpfeas heq
  exact ⟨p, hcert.2, heq⟩
