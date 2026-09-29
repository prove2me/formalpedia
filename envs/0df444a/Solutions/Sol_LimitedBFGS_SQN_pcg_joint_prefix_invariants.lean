-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_joint_prefix_invariants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T12:42:07.6668+00:00
-- url     : https://prove2.me/submissions/f8ef8c38-d2a3-4557-81d9-292c880039ba

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_exactStep_minimizes_grad
import Theorems.Thm_LimitedBFGS_SQN_pcg_grad_direction_key
import Theorems.Thm_LimitedBFGS_SQN_pcg_direction_A_conjugacy_step_pd
import Theorems.Thm_LimitedBFGS_SQN_pcg_direction_base
import Theorems.Thm_LimitedBFGS_SQN_pcg_direction_recursion
import Theorems.Thm_LimitedBFGS_SQN_exactStep_zero_gives_zero_dir

open Matrix
open LimitedBFGS.SQN

/-- **Simultaneous forward induction on three one-sided prefix invariants.**

Along the preconditioned conjugate gradient iteration (13) of Nocedal 1980, p. 777, with
the fixed symmetric positive definite preconditioner `H0` and exact line searches, for
every `k` all three of the following hold:

* `D(k)` : `g_k ⬝ᵥ d_j = 0`         for all `j < k`
* `G(k)` : `g_k ⬝ᵥ (H0 *ᵥ g_j) = 0` for all `j < k`
* `C(k)` : `d_k ⬝ᵥ (A *ᵥ d_j) = 0`  for all `j < k`

where `g_k = grad A b (pcgIter A b H0 x0 k).x` and `d_k = (pcgIter A b H0 x0 k).d`.

**Why the induction is well founded.** The step from `k` to `k + 1` consumes its
premises in the fixed order

    old C, old D, old G   ->   new D   ->   new G   ->   new C

so no invariant is ever established in isolation from itself, and no step needs a
hypothesis that is only available later in the same step. This is the acyclicity that
the isolated gap-two argument lacks.

**The three successor steps.** Writing `a_k = exactStep A b st_k.x st_k.d` and
`y_k = g_{k+1} - g_k = a_k (A *ᵥ d_k)`:

* *new D*, at `j = k`: exact line search gives `g_{k+1} ⬝ᵥ d_k = 0`. At `j < k`:
  `g_{k+1} ⬝ᵥ d_j = (g_k + a_k A *ᵥ d_k) ⬝ᵥ d_j`, whose two terms are old D and
  old C respectively.
* *new G*, at `j = 0`: `d_0 = -(H0 *ᵥ g_0)`, so new D makes `g_{k+1} ⬝ᵥ d_0 = 0`
  read as `- (g_{k+1} ⬝ᵥ H0 *ᵥ g_0)`. At `0 < j`: `H0 *ᵥ g_j = -d_j + beta d_{j-1}`
  and both dot products vanish by **new** D.
* *new C*, at `j = k`: the one-step `A`-conjugacy. At `j < k`: the `beta d_k` term
  vanishes by old C, and the remaining `T = (H0 *ᵥ g_{k+1}) ⬝ᵥ (A *ᵥ d_j)` is killed
  because `a_j T = g_{k+1} ⬝ᵥ H0 *ᵥ g_{j+1} - g_{k+1} ⬝ᵥ H0 *ᵥ g_j`, two columns of
  new G. When `a_j = 0` this reads as a division, so it needs the vanishing-step
  lemma; that dependency is the one place this proof reaches outside the three
  invariants.

The one input from outside the three invariants is `exactStep_zero_gives_zero_dir`,
used solely in the `a_j = 0` branch of new C, where it turns `a_j = 0` into `d_j = 0`
and hence `A *ᵥ d_j = 0`. That branch is the only place the three-invariant system
cannot close on its own: with `a_j = 0` the identity `g_{j+1} - g_j = a_j (A *ᵥ d_j)`
degenerates to `g_{j+1} = g_j`, making the two new-G columns the same equation and
leaving `T` unconstrained.

Nothing here needs termination, `pcg_step_coefficient`, or any global
orthogonality/conjugacy statement. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∀ k : ℕ,
      (∀ j < k, grad A b (pcgIter A b H₀ x₀ k).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d = 0) ∧
      (∀ j < k, grad A b (pcgIter A b H₀ x₀ k).x ⬝ᵥ
        (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) = 0) ∧
      (∀ j < k, (pcgIter A b H₀ x₀ k).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ j).d) = 0) := by
  classical
  have hA_tr : Aᵀ = A := (isHermitian_iff_isSymm.mp hA.isHermitian).eq
  have pair_comm_A : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
    intro u v
    have h := dotProduct_transpose_mulVec (A := A) (x := u) (y := v)
    rwa [hA_tr] at h
  have pair_comm_H : ∀ u v : Fin n → ℝ, u ⬝ᵥ (H₀ *ᵥ v) = v ⬝ᵥ (H₀ *ᵥ u) := by
    intro u v
    have h := dotProduct_transpose_mulVec (A := H₀) (x := u) (y := v)
    rwa [(isHermitian_iff_isSymm.mp hH₀.isHermitian).eq] at h
  -- The flipped orientations and the negation each successor is rewritten with.
  have hA_flip (u v : Fin n → ℝ) : (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v) := by
    rw [dotProduct_comm, pair_comm_A v u]
  have hH_flip (u v : Fin n → ℝ) : (H₀ *ᵥ u) ⬝ᵥ v = v ⬝ᵥ (H₀ *ᵥ u) := by
    rw [dotProduct_comm, pair_comm_H v u]
  have hneg (u v : Fin n → ℝ) : (-u) ⬝ᵥ v = -(u ⬝ᵥ v) := by
    rw [dotProduct_comm, dotProduct_neg, dotProduct_comm]
  have haff (a : ℝ) (x d : Fin n → ℝ) : grad A b (x + a • d) = grad A b x + a • (A *ᵥ d) := by
    simp only [grad, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    abel
  -- The realised successor iterate, and the GRADIENT SUCCESSOR identity built from it.
  have hxsuc (k : ℕ) : (pcgIter A b H₀ x₀ (Nat.succ k)).x
      = (pcgIter A b H₀ x₀ k).x
        + exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d
          • (pcgIter A b H₀ x₀ k).d := by simp only [pcgIter]
  have hgrad (k : ℕ) : grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x
      = grad A b (pcgIter A b H₀ x₀ k).x
        + exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d
          • (A *ᵥ (pcgIter A b H₀ x₀ k).d) := by rw [hxsuc, haff]
  -- The successor direction. `β` is parenthesised and typed because at Lean 4.33.1
  -- `•` is `infixr:73`, `⬝ᵥ` is `infixl:72` and `/` is `infixl:70`, so the unparenthesised
  -- `num ⬝ᵥ den / den ⬝ᵥ d • d` would parse `num ⬝ᵥ (den / (den ⬝ᵥ (d • d)))` and ask for
  -- `HDiv ℝ (Fin n → ℝ)`.
  have hdsuc (k : ℕ) : (pcgIter A b H₀ x₀ (Nat.succ k)).d
      = -(H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x)
        + (((grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x
              - grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ
            (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x))
          / ((grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x
              - grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ (pcgIter A b H₀ x₀ k).d))
          • (pcgIter A b H₀ x₀ k).d := by simp only [pcgIter]
  -- ONE-STEP GRADIENT IDENTITY: `g_{j+1} - g_j = a_j (A *ᵥ d_j)`.
  have hy (j : ℕ) :
      grad A b (pcgIter A b H₀ x₀ (Nat.succ j)).x - grad A b (pcgIter A b H₀ x₀ j).x
        = exactStep A b (pcgIter A b H₀ x₀ j).x (pcgIter A b H₀ x₀ j).d
          • (A *ᵥ (pcgIter A b H₀ x₀ j).d) := by rw [hgrad j, add_sub_cancel_left]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      cases k with
      | zero =>
        exact ⟨fun j hj => (Nat.not_lt_zero j hj).elim, fun j hj => (Nat.not_lt_zero j hj).elim,
          fun j hj => (Nat.not_lt_zero j hj).elim⟩
      | succ k =>
        have hprev := ih k (Nat.lt_succ_self k)
        -- **new D**: `g_{k+1} ⬝ᵥ d_j = 0` for `j < k + 1`.
        have hDnext : ∀ j < Nat.succ k, grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x
            ⬝ᵥ (pcgIter A b H₀ x₀ j).d = 0 := by
          intro j hj
          by_cases hjk : j = k
          · rw [hjk, hxsuc]
            exact exactStep_minimizes_grad A hA b _ _
          · have hjlt : j < k := by omega
            rw [hgrad k, add_dotProduct, smul_dotProduct, hA_flip,
              hprev.1 j hjlt, hprev.2.2 j hjlt]
            ring
        -- **new G**: `g_{k+1} ⬝ᵥ (H₀ *ᵥ g_j) = 0` for `j < k + 1`.
        have hGnext : ∀ j < Nat.succ k, grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x ⬝ᵥ
            (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) = 0 := by
          intro j hj
          by_cases hjz : j = 0
          · rw [hjz]
            have hbase := pcg_direction_base A hA b H₀ x₀ (Nat.succ k) (by omega)
            linarith [hbase, hDnext 0 (by omega)]
          · have hrec := pcg_direction_recursion A hA b H₀ x₀ (Nat.succ k) j (by omega) (by omega)
            dsimp only at hrec
            rw [hDnext j (by omega), hDnext (j - 1) (by omega)] at hrec
            simp only [mul_zero, add_zero] at hrec
            linarith [hrec]
        -- `hGnext` in the orientation the `C` successor consumes it.
        have hGflip (j : ℕ) (hj : j < Nat.succ k) :
            (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x) ⬝ᵥ
              grad A b (pcgIter A b H₀ x₀ j).x = 0 := by
          rw [dotProduct_comm, pair_comm_H]
          exact hGnext j hj
        -- **new C**: `d_{k+1} ⬝ᵥ (A *ᵥ d_j) = 0` for `j < k + 1`.
        have hCnext : ∀ j < Nat.succ k, (pcgIter A b H₀ x₀ (Nat.succ k)).d
            ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ j).d) = 0 := by
          intro j hj
          by_cases hjk : j = k
          · rw [hjk]
            exact pcg_direction_A_conjugacy_step_pd A hA b H₀ hH₀ x₀ k
          · have hjlt : j < k := by omega
            have hT : (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x)
                ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ j).d) = 0 := by
              by_cases haj : exactStep A b (pcgIter A b H₀ x₀ j).x (pcgIter A b H₀ x₀ j).d = 0
              · have hdz := exactStep_zero_gives_zero_dir A hA b H₀ hH₀ x₀ j haj
                simp [hdz]
              · have hmul : (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (Nat.succ k)).x)
                    ⬝ᵥ (exactStep A b (pcgIter A b H₀ x₀ j).x (pcgIter A b H₀ x₀ j).d
                      • (A *ᵥ (pcgIter A b H₀ x₀ j).d)) = 0 := by
                  rw [← hy j, dotProduct_sub, hGflip (Nat.succ j) (by omega), hGflip j hj]
                  ring
                rw [dotProduct_smul, smul_eq_mul] at hmul
                exact (mul_eq_zero.mp hmul).resolve_left haj
            rw [hdsuc, add_dotProduct, smul_dotProduct, hneg, hT, hprev.2.2 j hjlt]
            ring
        exact ⟨hDnext, hGnext, hCnext⟩
