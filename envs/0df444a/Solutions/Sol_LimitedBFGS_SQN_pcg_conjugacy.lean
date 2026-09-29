-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T03:10:04.289895+00:00
-- url     : https://prove2.me/submissions/372f4d97-fb94-494f-b5e5-9813bf1164bc

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_grad_orthogonality

open Matrix
open LimitedBFGS.SQN

/-- **Eq. (15), p. 777: `d_iᵀ y_j = 0` for `i ≠ j` along the PCG with fixed
preconditioner `H₀`.**

Write `g_k = grad A b (pcgIter A b H₀ x₀ k).x`, `d_k = (pcgIter … k).d` and
`y_k = g_{k+1} - g_k`. The proof is a strong induction on `i` in which each
step is discharged by one of four facts.

**(F1) The update is definitional.** For every `k`, `d_{k+1} = -(H₀ *ᵥ g_{k+1})
+ β • d_k`, so for every `q`

```lean
d_{k+1} ⬝ᵥ y_q = -(H₀ *ᵥ g_{k+1}) ⬝ᵥ y_q + β * (d_k ⬝ᵥ y_q)
```

This is only an *expansion*: the `β` summand is killed by the induction
hypothesis, never by cancellation, so the argument never divides by `y_k ⬝ᵥ d_k`.

**(F2) Hermitian transfer.** `H₀` is positive definite, hence symmetric, so
`dotProduct_mulVec` moves the matrix across and a dot product against `H₀ *ᵥ u`
may be read with the roles of the two vectors exchanged.

**(F3) Gradient orthogonality** is the single external input, and it is the
unproved reduction obligation below: `g_p ⬝ᵥ (H₀ *ᵥ g_q) = 0` for `p ≠ q`, the
classical PCG gradient-orthogonality theorem (eq. (16) first half, p. 777),
which is itself the open sibling target `LimitedBFGS.SQN.pcg_grad_orthogonality`.

**(G) The kill.** By (F2) and (F3),

```lean
(H₀ *ᵥ g_p) ⬝ᵥ y_q = (g_p ⬝ᵥ H₀ *ᵥ g_{q+1}) - (g_p ⬝ᵥ H₀ *ᵥ g_q) = 0
```

whenever `p ∉ {q, q+1}`. This covers **both** orderings of `i ≠ j` at once,
since the vanishing is asserted at the gradient index `p` and does not depend on
whether `p` lies below or above `q`; that is what forces the "for all indices"
reading of eq. (15).

**(YDEF)** `y_k = α_k • (A *ᵥ d_k)` with `α_k = exactStep A b x_k d_k`. This is
purely affine — `grad A b (x + α • d) = grad A b x + α • (A *ᵥ d)` — and needs
no exact-line-search property.

**(QKILL)** `y_k ⬝ᵥ d_k = 0` implies `y_k = 0`: by (YDEF) the left side is
`α_k * (d_k ⬝ᵥ A *ᵥ d_k)`, and `d_k ⬝ᵥ A *ᵥ d_k > 0` whenever `d_k ≠ 0` since
`A` is positive definite, so `α_k = 0`.

**The induction.** The base `i = 0` reads off `d₀ = -(H₀ *ᵥ g₀)` and applies (G).
For `i = k + 1` the hypothesis `hij : k + 1 ≠ q` is already available, so (G)
applies unless `k = q`; and `k = q` is exactly the **adjacent** case
`d_{k+1} ⬝ᵥ y_k = 0`, which is the one case (G) cannot reach. That case is
discharged by `β`'s own definition, split on `Q = y_k ⬝ᵥ d_k`: if `Q ≠ 0` the
cancellation `(P/Q) * Q = P` is exact, and if `Q = 0` then (QKILL) gives
`y_k = 0`, so `P = y_k ⬝ᵥ (H₀ *ᵥ g_{k+1}) = 0` and both sides vanish.

The single imported child (F3) is the reduction obligation; everything else in
this file is proved. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) (i j : ℕ) (hij : i ≠ j) :
    (pcgIter A b H₀ x₀ i).d ⬝ᵥ
      (grad A b (pcgIter A b H₀ x₀ (j + 1)).x - grad A b (pcgIter A b H₀ x₀ j).x) = 0 := by
  -- (F3): the single external input and the only reduction obligation.
  have HG : ∀ p q : ℕ, p ≠ q → grad A b (pcgIter A b H₀ x₀ p).x ⬝ᵥ
      (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ q).x) = 0 := by
    intro p q hpq
    exact pcg_grad_orthogonality A hA b H₀ hH₀ x₀ p q hpq
  -- (F2): `H₀` is positive definite, hence symmetric.
  have hH0T : H₀ᵀ = H₀ := by
    rw [← conjTranspose_eq_transpose_of_trivial (A := H₀)]
    exact hH₀.1.eq
  have hsym : ∀ u v : Fin n → ℝ, (H₀ *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (H₀ *ᵥ v) := by
    intro u v
    rw [dotProduct_mulVec, ← Matrix.vecMul_transpose, hH0T]
  -- (G): the preconditioned-gradient piece vanishes off `{q, q+1}`.
  have Hkill : ∀ p q : ℕ, p ≠ q → p ≠ q + 1 → (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ p).x) ⬝ᵥ
      (grad A b (pcgIter A b H₀ x₀ (q + 1)).x - grad A b (pcgIter A b H₀ x₀ q).x) = 0 := by
    intro p q h1 h2
    rw [dotProduct_sub, hsym, hsym]
    exact sub_eq_zero.mpr ((HG p (q + 1) h2).trans (HG p q h1).symm)
  -- (F1): the definitional update, as an identity for every `k` and `q`.
  have Hupd : ∀ (k q : ℕ), (pcgIter A b H₀ x₀ k.succ).d ⬝ᵥ
      (grad A b (pcgIter A b H₀ x₀ (q + 1)).x - grad A b (pcgIter A b H₀ x₀ q).x)
      = (-(H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ k.succ).x)) ⬝ᵥ
          (grad A b (pcgIter A b H₀ x₀ (q + 1)).x - grad A b (pcgIter A b H₀ x₀ q).x)
        + ((grad A b (pcgIter A b H₀ x₀ k.succ).x - grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ
            (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ k.succ).x)) /
          ((grad A b (pcgIter A b H₀ x₀ k.succ).x - grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ
            (pcgIter A b H₀ x₀ k).d) *
          ((pcgIter A b H₀ x₀ k).d ⬝ᵥ
            (grad A b (pcgIter A b H₀ x₀ (q + 1)).x - grad A b (pcgIter A b H₀ x₀ q).x)) := by
    intro k q
    -- Only the successor state's direction needs unfolding. Rewriting the
    -- whole goal with `simp only [pcgIter]` would also unfold the *step* index
    -- `q` and the `k.succ` index, which replaces the two dot products on the
    -- right by sums over the columns of `H₀` and `A` and leaves `ring` with
    -- `Finset.sum`s it cannot see through.
    have hdir : (pcgIter A b H₀ x₀ k.succ).d
        = -(H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ k.succ).x)
          + (((grad A b (pcgIter A b H₀ x₀ k.succ).x
              - grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ
              (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ k.succ).x)) /
            ((grad A b (pcgIter A b H₀ x₀ k.succ).x
              - grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ (pcgIter A b H₀ x₀ k).d))
            • (pcgIter A b H₀ x₀ k).d := by
      simp only [pcgIter]
    -- `hdir` puts the update `-v + (β) • w` in the **left** argument of the dot
    -- product. Mathlib provides the left-argument forms directly — `add_dotProduct`,
    -- `neg_dotProduct` and `smul_dotProduct` — so no `dotProduct_comm` detour
    -- is needed. `smul_eq_mul` turns the scalar action on `ℝ` into `*`.
    rw [hdir, add_dotProduct, neg_dotProduct, smul_dotProduct, smul_eq_mul]
  -- (YDEF): the purely affine step identity.
  have hydef : ∀ k : ℕ, (grad A b (pcgIter A b H₀ x₀ k.succ).x
      - grad A b (pcgIter A b H₀ x₀ k).x)
      = exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d
        • (A *ᵥ (pcgIter A b H₀ x₀ k).d) := by
    intro k
    -- `grad A b v = A *ᵥ v + b` is affine in `v`, so for every step length `α`
    --   grad A b (x + α • d) = grad A b x + α • (A *ᵥ d).
    -- This is the whole content of (YDEF), and it uses no exact-line-search
    -- property: only `mulVec_add` (sum in the argument) and `mulVec_smul`.
    have haffine : ∀ (x d : Fin n → ℝ) (α : ℝ),
        grad A b (x + α • d) - grad A b x = α • (A *ᵥ d) := by
      intro x d α
      simp only [grad, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_add,
        Matrix.mulVec_smul]
      ring
    -- One step of the recursion: the successor state's `x` is exactly
    -- `x_k + exactStep … • d_k`, so `haffine` applies verbatim.
    simpa only [pcgIter] using haffine (pcgIter A b H₀ x₀ k).x
      (pcgIter A b H₀ x₀ k).d
      (exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d)
  -- (QKILL): `y_k ⬝ᵥ d_k = 0` forces `y_k = 0`.
  have hyzero : ∀ k : ℕ, (grad A b (pcgIter A b H₀ x₀ k.succ).x
      - grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ (pcgIter A b H₀ x₀ k).d = 0 →
      grad A b (pcgIter A b H₀ x₀ k.succ).x - grad A b (pcgIter A b H₀ x₀ k).x = 0 := by
    intro k hk
    -- By (YDEF) the gradient difference is `α_k • (A *ᵥ d_k)`, so the dot
    -- product with `d_k` is `(α_k • (A *ᵥ d_k)) ⬝ᵥ d_k`. `smul_dotProduct`
    -- is the left-argument form, and `smul_eq_mul` turns the scalar action on
    -- `ℝ` into the multiplication `α_k * (d_k ⬝ᵥ A *ᵥ d_k)` that
    -- `mul_eq_zero` can destructure.
    rw [hydef k, smul_dotProduct, dotProduct_comm, smul_eq_mul] at hk
    by_cases hd : (pcgIter A b H₀ x₀ k).d = 0
    · -- The direction vanishes, so the right-hand side of (QKILL) is
      -- `α_k • (A *ᵥ 0) = 0`.
      rw [hydef k, hd, Matrix.mulVec_zero, smul_zero]
    · -- `hA.dotProduct_mulVec_pos hd` is stated as `0 < x ⬝ᵥ A *ᵥ x`, with the
      -- vector on the **left**; the hypothesis `hk` produced
      -- `α_k * (d_k ⬝ᵥ A *ᵥ d_k)` in exactly that orientation.
      have hpos := hA.dotProduct_mulVec_pos hd
      have hex : exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d = 0 := by
        by_contra hc
        rw [mul_eq_zero] at hk
        rcases hk with hα | hden
        · exact absurd hα hc
        · exact absurd hden (ne_of_gt hpos)
      -- The goal names the successor iterate and not `exactStep`, so the
      -- equation is consumed through a `calc` rather than by a rewrite that
      -- would have to match an unreduced `exactStep`.
      rw [hydef k, hex, zero_smul]
  -- The adjacent case `d_{k+1} ⬝ᵥ y_k = 0`, which is the one (G) cannot reach.
  -- The scalar identity behind `β`'s own definition: with `P = u ⬝ᵥ v` and
  -- `Q = v ⬝ᵥ w` the update is `-(u ⬝ᵥ v) + (v ⬝ᵥ u) / Q * (w ⬝ᵥ v)`, and
  -- `dotProduct_comm` turns the numerator and the trailing factor into `P`
  -- and `Q` themselves, so `field_simp` cancels the denominator exactly.
  -- Stating it once here keeps the two dot products of `y_k` in a single
  -- syntactic form, which is what lets `ring` see the cancellation below.
  have hcancel : ∀ (u v w : Fin n → ℝ), v ⬝ᵥ w ≠ 0 →
      -(u ⬝ᵥ v) + (v ⬝ᵥ u) / (v ⬝ᵥ w) * (w ⬝ᵥ v) = 0 := by
    intro u v w hQ
    rw [dotProduct_comm v u, dotProduct_comm w v]
    field_simp [hQ]
    ring
  have Hadj : ∀ k : ℕ, (pcgIter A b H₀ x₀ k.succ).d ⬝ᵥ
      (grad A b (pcgIter A b H₀ x₀ k.succ).x - grad A b (pcgIter A b H₀ x₀ k).x) = 0 := by
    intro k
    by_cases hQ : (grad A b (pcgIter A b H₀ x₀ k.succ).x
        - grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ (pcgIter A b H₀ x₀ k).d = 0
    · -- Degenerate branch: (QKILL) gives `y_k = 0`, so both the gradient
      -- difference and the `β` numerator vanish and the whole update is `0`.
      have hy : grad A b (pcgIter A b H₀ x₀ k.succ).x
          - grad A b (pcgIter A b H₀ x₀ k).x = 0 := hyzero k hQ
      simp only [hy, sub_self, dotProduct_zero, zero_dotProduct, zero_div,
        zero_mul, neg_zero, add_zero]
    · -- Nondegenerate branch: `field_simp` cancels the denominator of `β`
      -- exactly once, and `ring` closes the residual identity.
      -- `Hupd` puts the `β` numerator and the `d_k ⬝ᵥ y_k` factor on the
      -- board, and `neg_dotProduct` moves the sign of the leading
      -- `-(H₀ *ᵥ g_{k+1})` inside the dot product, leaving exactly the
      -- identity `hcancel` states.
      rw [Hupd k k, neg_dotProduct, Nat.succ_eq_add_one]
      exact hcancel _ _ _ hQ
  -- Strong induction on `i`.
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          -- `d₀ = -(H₀ *ᵥ g₀)`, and `neg_dotProduct` is the left-argument form.
          -- `hij` is already specialised to `0 ≠ j` here, which is what (G)
          -- needs; stating the base case above the induction would have left
          -- it quantified over the outer `i` and forced the wrong hypothesis.
          have heq : (pcgIter A b H₀ x₀ 0).d = -(H₀ *ᵥ grad A b x₀) := by
            simp only [pcgIter]
          have hg0 : (pcgIter A b H₀ x₀ 0).x = x₀ := by
            simp only [pcgIter]
          -- (G) at `p = 0`, that is `(H₀ *ᵥ g₀) ⬝ᵥ y_j = 0`, is exactly
          -- `Hkill 0 j`, read in the `(H₀ *ᵥ g) ⬝ᵥ y` orientation. `HG` is
          -- not used here: its gradient index is a bound variable, so it
          -- cannot be instantiated at `0` by a rewrite — but `Hkill` already
          -- carries (G) at `p = 0` with that index fixed.
          have hk0 := Hkill 0 j hij (by omega)
          rw [dotProduct_sub, hsym, hsym, hg0] at hk0
          -- `heq` supplies `d₀ = -(H₀ *ᵥ g₀)` and, by the same `pcgIter`
          -- equation, exposes the state's `x` as `x₀`; `neg_dotProduct` then
          -- moves the sign inside so the two statements coincide.
          rw [heq, neg_dotProduct, dotProduct_sub, hsym, hsym]
          -- Only the sign bookkeeping is left: `hk0` is `P - Q - 0 = 0` and
          -- the goal is `-(P - Q) = 0` for the same two dot products `P` and
          -- `Q`, already split by the `dotProduct_sub` above.
          linarith [hk0]
      | succ k =>
          by_cases hkj : k = j
          -- `Hadj k` speaks about `y_k` and the goal about `y_j`; the
          -- equation `hkj` is what identifies them.
          · exact hkj ▸ Hadj k
          -- (G) at `p = k + 1, q = j` needs `k + 1 ≠ j` — which is `hij` in
          -- this branch — and `k + 1 ≠ j + 1`, which is `hkj` transported
          -- across `Nat.succ`. `(Hkill · j)` is stated with `j + 1`, while
          -- the goal writes `j + 1` as well. The sign of the leading
          -- `-(H₀ *ᵥ g_{k+1})` term is moved inside the dot product first, so
          -- that `Hkill`'s `(H₀ *ᵥ g) ⬝ᵥ y` shape actually occurs; the
          -- residual `ring` step then only has to add the two signs.
          -- `ih k` needs `k ≠ j` and `k ≤ j`; the first is `hkj` outright and
          -- the second follows from `hij : k + 1 ≠ j`.
          · rw [Hupd k j, ih k (by omega) hkj, neg_dotProduct,
              Hkill k.succ j hij (by omega)]
            ring
