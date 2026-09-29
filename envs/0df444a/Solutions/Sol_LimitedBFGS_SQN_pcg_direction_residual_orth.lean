-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_direction_residual_orth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T08:59:56.585546+00:00
-- url     : https://prove2.me/submissions/139de07b-a70a-4f9a-82f3-13cc8cd21bc4

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_direction_A_conjugacy_step_pd

open Matrix
open LimitedBFGS.SQN

/-- Eq. (16), p. 777: the residual left over by the direction recurrence,

    r_k := H₀ *ᵥ g_k + d_k,

is orthogonal, in the `A` form, to the direction used at step `k`:

    r_k ⬝ᵥ (A *ᵥ d_k) = 0.

**Proof.** At `k = 0` the recurrence is absent: the zeroth clause of the
iteration gives `d_0 = -(H₀ *ᵥ g_0)` exactly, so `r_0 = 0` and there is nothing
to prove. At `k = j + 1` the direction recurrence
`d_{j+1} = -(H₀ *ᵥ g_{j+1}) + beta_j * d_j` gives `r_{j+1} = beta_j * d_j`, so

    r_{j+1} ⬝ᵥ (A *ᵥ d_{j+1}) = beta_j (d_j ⬝ᵥ (A *ᵥ d_{j+1}))
                            = beta_j (d_{j+1} ⬝ᵥ (A *ᵥ d_j))     [`A` symmetric]
                            = 0

by the already-proved child `pcg_direction_A_conjugacy_step_pd`. The step
coefficient `beta_j` needs no hypothesis: it is the quotient the definition
itself forms, and it is only ever multiplied against something already known to
vanish, so the possibly-zero denominator `y_j ⬝ᵥ d_j` never has to be
discharged.

**Why it matters.** This is what makes the *adjacent* case of eq. (16)'s first
relation, `g_{k+1} ⬝ᵥ (H₀ *ᵥ g_k) = 0`, a one-step identity rather than part of
an induction: the term that would otherwise survive the step is exactly
`a_k (r_k ⬝ᵥ (A *ᵥ d_k))`, and this lemma kills it. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ)
    (k : ℕ) :
    (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ k).x + (pcgIter A b H₀ x₀ k).d) ⬝ᵥ
        (A *ᵥ (pcgIter A b H₀ x₀ k).d) = 0 := by
  classical
  cases k with
  | zero =>
      have h0 : pcgIter A b H₀ x₀ 0 = ⟨x₀, -(H₀ *ᵥ grad A b x₀)⟩ := by
        simp [pcgIter]
      rw [h0]
      simp
  | succ j =>
      set stj := pcgIter A b H₀ x₀ j with hstj
      set dj := stj.d with hdj
      set bj := exactStep A b stj.x stj.d with hbj
      set xj := stj.x + bj • dj with hxj
      set gj := grad A b xj with hgj
      set Hj := H₀ *ᵥ gj with hHj
      set yj := gj - grad A b stj.x with hyj
      have hstep : pcgIter A b H₀ x₀ (j + 1)
          = ⟨xj, -Hj + ((yj ⬝ᵥ Hj) / (yj ⬝ᵥ dj)) • dj⟩ := by
        simp only [pcgIter, hstj, hdj, hbj, hxj, hgj, hHj, hyj]
      have hA_tr : Aᵀ = A := (isHermitian_iff_isSymm.mp hA.isHermitian).eq
      have hsymm : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
        intro u v
        have h := dotProduct_transpose_mulVec (A := A) (x := u) (y := v)
        rwa [hA_tr] at h
      -- The proved one-step `A`-conjugacy, read at `j`.
      have hac : (pcgIter A b H₀ x₀ (j + 1)).d ⬝ᵥ
          (A *ᵥ (pcgIter A b H₀ x₀ j).d) = 0 :=
        pcg_direction_A_conjugacy_step_pd A hA b H₀ hH₀ x₀ j
      -- `hsymm dj d_(j+1) : d_j ⬝ᵥ (A *ᵥ d_(j+1)) = d_(j+1) ⬝ᵥ (A *ᵥ d_j)`, and the right
      -- side is exactly `hac`. So `d_j ⬝ᵥ (A *ᵥ d_(j+1)) = 0` is the proved conjugacy read
      -- across the symmetry of the `A` form.
      have hAdj : dj ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ (j + 1)).d) = 0 := by
        calc dj ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ (j + 1)).d)
            = (pcgIter A b H₀ x₀ (j + 1)).d ⬝ᵥ (A *ᵥ dj) := hsymm _ _
          _ = (pcgIter A b H₀ x₀ (j + 1)).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ j).d) := by
                rw [hdj, hstj]
          _ = 0 := hac
      -- The residual at `j + 1` is exactly `beta_j * d_j`. This is stated separately so
      -- that rewriting it does not also unfold the `d_(j+1)` that `hAdj` talks about.
      have hres : H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (j + 1)).x
            + (pcgIter A b H₀ x₀ (j + 1)).d
          = ((yj ⬝ᵥ Hj) / (yj ⬝ᵥ dj)) • dj := by
        rw [hstep]
        -- the left summand is `H0 *ᵥ grad A b xj`, which is `Hj` by `hHj`
        rw [← hHj]
        congr 1
        ext i
        simp
      rw [hres, smul_dotProduct, smul_eq_mul, hAdj, mul_zero]
