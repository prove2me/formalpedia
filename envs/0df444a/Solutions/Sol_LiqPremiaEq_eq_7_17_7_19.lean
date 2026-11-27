-- Prove2me | solution 1 for LiqPremiaEq.eq_7_17_7_19
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-27T02:03:44.019991+00:00
-- url     : https://prove2.me/submissions/f1670ded-addb-4790-8428-9790a5372de3

import Mathlib
import Definitions.Def_LiqPremiaEq_Gam

open Matrix

open LiqPremiaEq

/-
  Outline for (7.17)-(7.19): direct componentwise computation from the
  definitions (3.4) gbar, Lemma 4.4 cvec, (4.7) Gam.
  N = (M : ℝ) + 1, γᴺ = γ (Fin.last M).

  Structure: three scalar/sum identities (lpe_sum_inner, lpe_gbar_sum,
  lpe_sum_one_minus) plus two pure field identities (lpe_alg_718, lpe_alg_717)
  plus two matrix row computations (lpe_row_718, lpe_row_717).
  Two trivial glue lemmas (lpe_cvec_sum, lpe_v_shift) are proved here.
  `solution` assembles them; each (7.17)/(7.18)/(7.19) follows in ~5 lines.
-/

namespace P2MHole01_dfa43afe
theorem solution {M : ℕ} (γ : Fin (M + (1 : ℕ)) → ℝ) (hγ : ∀ (n : Fin (M + (1 : ℕ))), (0 : ℝ) < γ n) :
  ∑ n : Fin M, ((1 : ℝ) / γ n.castSucc - (1 : ℝ) / γ (Fin.last M)) =
    ∑ n : Fin (M + (1 : ℕ)), (1 : ℝ) / γ n - (↑M + (1 : ℝ)) / γ (Fin.last M) := by
  have hL : ∑ n : Fin M, ((1 : ℝ) / γ n.castSucc - (1 : ℝ) / γ (Fin.last M)) =
      (∑ n : Fin M, (1 : ℝ) / γ n.castSucc) - (∑ n : Fin M, (1 : ℝ) / γ (Fin.last M)) := by
    rw [Finset.sum_sub_distrib]
  rw [hL]
  have hc : ∑ n : Fin M, (1 : ℝ) / γ (Fin.last M) = (M : ℝ) * ((1 : ℝ) / γ (Fin.last M)) := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [hc]
  have hR : ∑ n : Fin (M + (1 : ℕ)), (1 : ℝ) / γ n =
      (∑ n : Fin M, (1 : ℝ) / γ n.castSucc) + (1 : ℝ) / γ (Fin.last M) := by
    rw [Fin.sum_univ_castSucc]
  rw [hR]
  rw [← mul_one_div]
  ring
end P2MHole01_dfa43afe

/-- (7.19) inner sum: ∑_{Fin M} (1/γⁿ − 1/γᴺ) = ∑_{Fin (M+1)} 1/γ − N/γᴺ.
Finite-sum identity (no gbar, no cvec). -/
lemma lpe_sum_inner {M : ℕ} (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) :
    (∑ n : Fin M, (1 / γ n.castSucc - 1 / γ (Fin.last M))) =
    (∑ n : Fin (M + 1), 1 / γ n) - ((M : ℝ) + 1) / γ (Fin.last M) := by
  (first | exact P2MHole01_dfa43afe.solution γ hγ | (apply P2MHole01_dfa43afe.solution <;> assumption))

namespace P2MHole02_c1ad29b8
theorem solution {M : ℕ} (γ : Fin (M + (1 : ℕ)) → ℝ) (hγ : ∀ (n : Fin (M + (1 : ℕ))), (0 : ℝ) < γ n) :
  gbar γ * ∑ n : Fin (M + (1 : ℕ)), (1 : ℝ) / γ n = (1 : ℝ) := by
  dsimp [gbar]
  have hpos : 0 < ∑ n : Fin (M + (1 : ℕ)), (1 : ℝ) / γ n := by
    apply Finset.sum_pos
    · intro n _
      exact div_pos one_pos (hγ n)
    · exact ⟨Fin.last M, Finset.mem_univ _⟩
  field_simp [Ne.symm hpos.ne']
end P2MHole02_c1ad29b8

/-- (3.4): the aggregate risk aversion satisfies gbar · (∑ 1/γ) = 1. -/
lemma lpe_gbar_sum {M : ℕ} (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) :
    gbar γ * (∑ n : Fin (M + 1), 1 / γ n) = 1 := by
  (first | exact P2MHole02_c1ad29b8.solution γ hγ | (apply P2MHole02_c1ad29b8.solution <;> assumption))

namespace P2MHole03_f4fddfee
theorem solution {M : ℕ} (γ : Fin (M + (1 : ℕ)) → ℝ) (hγ : ∀ (n : Fin (M + (1 : ℕ))), (0 : ℝ) < γ n) :
  ∑ m : Fin M, ((1 : ℝ) - γ (Fin.last M) / γ m.castSucc) =
    ↑M + (1 : ℝ) - γ (Fin.last M) * ∑ n : Fin (M + (1 : ℕ)), (1 : ℝ) / γ n := by
  let gN : ℝ := γ (Fin.last M)
  have hN0 : gN ≠ 0 := (hγ (Fin.last M)).ne'
  have hLHS : (∑ m : Fin M, ((1 : ℝ) - gN / γ m.castSucc)) =
      (↑M : ℝ) - gN * ∑ m : Fin M, (1 : ℝ) / γ m.castSucc := by
    have h1 : ∑ m : Fin M, ((1 : ℝ) - gN / γ m.castSucc) =
        ∑ m : Fin M, (1 : ℝ) - ∑ m : Fin M, gN / γ m.castSucc := by
      rw [Finset.sum_sub_distrib]
    have h2 : ∑ m : Fin M, gN / γ m.castSucc = gN * ∑ m : Fin M, (1 : ℝ) / γ m.castSucc := by
      have h3 : ∑ m : Fin M, gN / γ m.castSucc = ∑ m : Fin M, gN * (1 / γ m.castSucc) := by
        simp [div_eq_mul_inv]
      rw [h3, ← Finset.mul_sum]
    rw [h1, h2]
    simp [Finset.sum_const, Fintype.card_fin]
  have hsplit : (∑ n : Fin (M + (1 : ℕ)), (1 : ℝ) / γ n) =
      (∑ m : Fin M, (1 : ℝ) / γ m.castSucc) + (1 : ℝ) / gN := by
    rw [Fin.sum_univ_castSucc]
  have hRHS : (↑M : ℝ) + 1 - gN * ∑ n : Fin (M + (1 : ℕ)), (1 : ℝ) / γ n =
      (↑M : ℝ) - gN * ∑ m : Fin M, (1 : ℝ) / γ m.castSucc := by
    rw [hsplit, mul_add, mul_one_div, div_self hN0]
    ring
  calc
    ∑ m : Fin M, ((1 : ℝ) - γ (Fin.last M) / γ m.castSucc) =
        ∑ m : Fin M, ((1 : ℝ) - gN / γ m.castSucc) := rfl
    _ = (↑M : ℝ) - gN * ∑ m : Fin M, (1 : ℝ) / γ m.castSucc := hLHS
    _ = (↑M : ℝ) + 1 - gN * ∑ n : Fin (M + (1 : ℕ)), (1 : ℝ) / γ n := by
      rw [← hRHS]
end P2MHole03_f4fddfee

/-- (7.17) sum that appears in the row of Γ: ∑_{Fin M} (1 − γᴺ/γᵐ) = N − γᴺ·(∑ 1/γ).
Finite-sum identity (no gbar, no cvec). -/
lemma lpe_sum_one_minus {M : ℕ} (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) :
    (∑ m : Fin M, (1 - γ (Fin.last M) / γ m.castSucc)) =
    ((M : ℝ) + 1) - γ (Fin.last M) * (∑ n : Fin (M + 1), 1 / γ n) := by
  (first | exact P2MHole03_f4fddfee.solution γ hγ | (apply P2MHole03_f4fddfee.solution <;> assumption))

namespace P2MHole04_af4652cc
theorem solution (γn γN g N : ℝ) (hγn : (0 : ℝ) < γn) (hγN : (0 : ℝ) < γN) (hN : (0 : ℝ) < N) :
  γn * (g * ((1 : ℝ) / γn - (1 : ℝ) / γN)) - (γn - γN) / N * ((1 : ℝ) - g * N / γN) = (γN - γn) / N := by
  grind
end P2MHole04_af4652cc

/-- (7.18) final field algebra: with cₙ = g·(1/γₙ − 1/γᴺ) and S = 1 − gN/γᴺ
(the value of (7.19)),  γₙ·cₙ − (γₙ − γᴺ)/N · S = (γᴺ − γₙ)/N. -/
lemma lpe_alg_718 (γn γN g N : ℝ) (hγn : 0 < γn) (hγN : 0 < γN) (hN : 0 < N) :
    γn * (g * (1 / γn - 1 / γN)) - (γn - γN) / N * (1 - g * N / γN) = (γN - γn) / N := by
  (first | exact P2MHole04_af4652cc.solution γn γN g N hγn hγN hN | (apply P2MHole04_af4652cc.solution <;> assumption))

namespace P2MHole05_afb0b1f2
theorem solution (g S γN N : ℝ) (hprod : g * S = (1 : ℝ)) (hN : (0 : ℝ) < N) :
  g - g / N * (N - γN * S) = γN / N := by
  grind
end P2MHole05_afb0b1f2

/-- (7.17) final field algebra: with g = gbar and S = ∑1/γ, g·S = 1 and N > 0
(earlier version without 0 < N was false at N = 0) imply
g − (g/N)·(N − γᴺ·S) = γᴺ/N. -/
lemma lpe_alg_717 (g S γN N : ℝ) (hprod : g * S = 1) (hN : 0 < N) :
    g - g / N * (N - γN * S) = γN / N := by
  (first | exact P2MHole05_afb0b1f2.solution g S γN N hprod hN | (apply P2MHole05_afb0b1f2.solution <;> assumption))

namespace P2MHole06_52ef5d63
theorem solution {M : ℕ} (γ : Fin (M + (1 : ℕ)) → ℝ) (hγ : ∀ (n : Fin (M + (1 : ℕ))), (0 : ℝ) < γ n)
  (n : Fin M) :
  ((Gam γ)ᵀ *ᵥ cvec γ) n =
    γ n.castSucc * cvec γ n - (γ n.castSucc - γ (Fin.last M)) / (↑M + (1 : ℝ)) * ∑ m : Fin M, cvec γ m := by
  set v : Fin M → ℝ := cvec γ with hv
  set N : ℝ := (M : ℝ) + 1
  set A : Matrix (Fin M) (Fin M) ℝ := Matrix.diagonal (fun k => γ k.castSucc)
  set B : Matrix (Fin M) (Fin M) ℝ := (1 / N) • Matrix.of (fun (_ : Fin M) (m : Fin M) => γ m.castSucc - γ (Fin.last M))
  have hGam : Gam γ = A - B := by
    dsimp only [Gam, A, B]
  -- (Bᵀ) n m = B m n = (1/N) * (γ n - γ last), constant in m.
  have hBmn : ∀ m : Fin M, B m n = (1 / N) * (γ n.castSucc - γ (Fin.last M)) := by
    intro m
    dsimp only [B]
    rw [Matrix.smul_apply, Matrix.of_apply]
    <;> ring
  -- (Aᵀ *ᵥ v) n = γ n * v n, since A is diagonal (so Aᵀ = A).
  have hA1 : (Aᵀ *ᵥ v) n = γ n.castSucc * v n := by
    dsimp only [A]
    rw [Matrix.diagonal_transpose, Matrix.mulVec_diagonal]
    <;> simp
  -- (Bᵀ *ᵥ v) n = (γ n - γ last)/N * ∑ v m.
  have hB1 : (Bᵀ *ᵥ v) n = (γ n.castSucc - γ (Fin.last M)) / N * ∑ m : Fin M, v m := by
    calc
      (Bᵀ *ᵥ v) n
        = ∑ m : Fin M, (Bᵀ) n m * v m := by
            rw [Matrix.mulVec_apply_eq_sum]
        _ = ∑ m : Fin M, B m n * v m := by
            simp [Matrix.transpose_apply]
        _ = ∑ m : Fin M, (1 / N) * (γ n.castSucc - γ (Fin.last M)) * v m := by
            simp [hBmn]
        _ = (1 / N) * (γ n.castSucc - γ (Fin.last M)) * ∑ m : Fin M, v m := by
            rw [← Finset.mul_sum]
            <;> ring_nf
        _ = (γ n.castSucc - γ (Fin.last M)) / N * ∑ m : Fin M, v m := by
            ring
  calc
    ((Gam γ)ᵀ *ᵥ cvec γ) n
      = ((A - B)ᵀ *ᵥ v) n := by
          rw [hGam, ← hv]
      _ = (Aᵀ *ᵥ v) n - (Bᵀ *ᵥ v) n := by
          rw [Matrix.transpose_sub, Matrix.sub_mulVec]
          <;> simp
      _ = γ n.castSucc * v n - (γ n.castSucc - γ (Fin.last M)) / N * ∑ m : Fin M, v m := by
          rw [hA1, hB1]
      _ = γ n.castSucc * cvec γ n - (γ n.castSucc - γ (Fin.last M)) / N * ∑ m : Fin M, cvec γ m := by
          simp only [hv]
end P2MHole06_52ef5d63

/-- (7.18) row computation: (Γᵀc)ₙ = γⁿ·cₙ − (γⁿ − γᴺ)/N · ∑ₘ cₘ, computed
from the definition (4.7) of Gam (row n of the transpose). -/
-- riskiest
lemma lpe_row_718 {M : ℕ} (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) (n : Fin M) :
    ((Gam γ)ᵀ *ᵥ cvec γ) n =
      γ n.castSucc * cvec γ n -
        (γ n.castSucc - γ (Fin.last M)) / ((M : ℝ) + 1) * (∑ m : Fin M, cvec γ m) := by
  (first | exact P2MHole06_52ef5d63.solution γ hγ n | (apply P2MHole06_52ef5d63.solution <;> assumption))

namespace P2MHole07_3ab82bc8
/-! Entry of the matrix Γ (eq. 4.7): Γₙₖ = γⁿ δₙₖ − (1/N)(γᵏ − γᴺ), with N = M + 1. -/
theorem sol_entry {M : ℕ} (γ : Fin (M + (1 : ℕ)) → ℝ) (n k : Fin M) :
    (Gam γ) n k =
      (if n = k then γ n.castSucc else 0) - 1 / ((M : ℝ) + 1) * (γ k.castSucc - γ (Fin.last M)) := by
  simp [Gam, Matrix.diagonal, Matrix.smul_apply, Matrix.of_apply, Matrix.sub_apply]

/-! The diagonal part of (Γ v)ₙ: only the k = n term survives and equals γ̄. -/
theorem sol_diag {M : ℕ} (γ : Fin (M + (1 : ℕ)) → ℝ)
    (hγ : ∀ (n : Fin (M + (1 : ℕ))), (0 : ℝ) < γ n) (n : Fin M) :
    ∑ k : Fin M, (if n = k then γ n.castSucc else 0) * (gbar γ / γ k.castSucc) = gbar γ := by
  have h1 : (∑ k : Fin M, (if n = k then γ n.castSucc else 0) * (gbar γ / γ k.castSucc)) =
      ∑ k : Fin M, (if n = k then gbar γ else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hnn : n = k
    · simp [hnn]
      field_simp [(hγ k.castSucc).ne']
    · simp [hnn]
  rw [h1]
  simp [Finset.sum_ite_eq]

/-! Pointwise: (1/N)(γₖ − γᴺ)(γ̄/γₖ) = (γ̄/N)(1 − γᴺ/γₖ), for 0 < γₖ, N = M + 1 > 0. -/
theorem sol_point {M : ℕ} (γ : Fin (M + (1 : ℕ)) → ℝ)
    (hγ : ∀ (n : Fin (M + (1 : ℕ))), (0 : ℝ) < γ n) (k : Fin M) :
    1 / ((M : ℝ) + 1) * (γ k.castSucc - γ (Fin.last M)) * (gbar γ / γ k.castSucc) =
      gbar γ / ((M : ℝ) + 1) * ((1 : ℝ) - γ (Fin.last M) / γ k.castSucc) := by
  have hn : γ k.castSucc ≠ 0 := (hγ k.castSucc).ne'
  field_simp [hn]

/-! The rank-one part of (Γ v)ₙ: factor γ̄/N out of the sum. -/
theorem sol_factor {M : ℕ} (γ : Fin (M + (1 : ℕ)) → ℝ)
    (hγ : ∀ (n : Fin (M + (1 : ℕ))), (0 : ℝ) < γ n) :
    (∑ k : Fin M, 1 / ((M : ℝ) + 1) * (γ k.castSucc - γ (Fin.last M)) * (gbar γ / γ k.castSucc)) =
      gbar γ / (↑M + (1 : ℝ)) * ∑ k : Fin M, ((1 : ℝ) - γ (Fin.last M) / γ k.castSucc) := by
  -- Pointwise: each summand becomes (gbar/N)(1 − γᴺ/γₖ).
  have h1 : (∑ k : Fin M, 1 / ((M : ℝ) + 1) * (γ k.castSucc - γ (Fin.last M)) * (gbar γ / γ k.castSucc)) =
      ∑ k : Fin M, (gbar γ / ((M : ℝ) + 1)) * ((1 : ℝ) - γ (Fin.last M) / γ k.castSucc) := by
    rw [Finset.sum_congr rfl (fun k _ => sol_point γ hγ k)]
  rw [h1]
  -- Factor the scalar gbar/N out of the sum (N = (M : ℝ) + 1 = ↑M + 1 is the same real).
  rw [← Finset.mul_sum]

theorem solution {M : ℕ} (γ : Fin (M + (1 : ℕ)) → ℝ) (hγ : ∀ (n : Fin (M + (1 : ℕ))), (0 : ℝ) < γ n)
  (n : Fin M) :
  (Gam γ *ᵥ fun (k : Fin M) => gbar γ / γ k.castSucc) n =
    gbar γ - gbar γ / (↑M + (1 : ℝ)) * ∑ m : Fin M, ((1 : ℝ) - γ (Fin.last M) / γ m.castSucc) := by
  -- (M *ᵥ v) n is definitionally ∑ k, M n k * v k (the ⬝ᵥ operator is a sum).
  change ∑ k : Fin M, (Gam γ) n k * (gbar γ / γ k.castSucc) =
      gbar γ - gbar γ / (↑M + (1 : ℝ)) * ∑ m : Fin M, ((1 : ℝ) - γ (Fin.last M) / γ m.castSucc)
  -- Substitute the entry of Γ, distribute the product, and split the sum.
  have hsplit :
      (∑ k : Fin M, (Gam γ) n k * (gbar γ / γ k.castSucc)) =
      (∑ k : Fin M, (if n = k then γ n.castSucc else 0) * (gbar γ / γ k.castSucc)) -
        (∑ k : Fin M, 1 / ((M : ℝ) + 1) * (γ k.castSucc - γ (Fin.last M)) * (gbar γ / γ k.castSucc)) := by
    simp [sol_entry, sub_mul, Finset.sum_sub_distrib]
  rw [hsplit, sol_diag γ hγ n, sol_factor γ hγ]
end P2MHole07_3ab82bc8

/-- (7.17) row computation: the n-th row of Γ applied to the shifted vector
(γ̄/γⁿ)_{n} gives γ̄ − (γ̄/N)·∑ₘ(1 − γᴺ/γᵐ). -/
lemma lpe_row_717 {M : ℕ} (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) (n : Fin M) :
    (Gam γ *ᵥ (fun k : Fin M => gbar γ / γ k.castSucc)) n =
      gbar γ - (gbar γ / ((M : ℝ) + 1)) * (∑ m : Fin M, (1 - γ (Fin.last M) / γ m.castSucc)) := by
  (first | exact P2MHole07_3ab82bc8.solution γ hγ n | (apply P2MHole07_3ab82bc8.solution <;> assumption))

/-- ∑ₙ cₙ = γ̄·∑ₙ(1/γⁿ − 1/γᴺ): factor γ̄ out of the definition of c. -/
lemma lpe_cvec_sum {M : ℕ} (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) :
    (∑ n : Fin M, cvec γ n) =
    gbar γ * (∑ n : Fin M, (1 / γ n.castSucc - 1 / γ (Fin.last M))) := by
  dsimp [cvec]
  rw [← Finset.mul_sum]

/-- cₙ + γ̄/γᴺ = γ̄/γⁿ: the shifted vector of (7.17) is exactly (γ̄/γⁿ). -/
lemma lpe_v_shift {M : ℕ} (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) (n : Fin M) :
    cvec γ n + gbar γ / γ (Fin.last M) = gbar γ / γ n.castSucc := by
  rw [cvec, one_div, one_div]
  ring_nf

theorem solution {M : ℕ} (hM : 1 ≤ M) (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) :
    Gam γ *ᵥ (cvec γ + (gbar γ / γ (Fin.last M)) • (fun _ => (1 : ℝ)))
        = (γ (Fin.last M) / ((M : ℝ) + 1)) • (fun _ => (1 : ℝ)) ∧
      (∀ n : Fin M, ((Gam γ)ᵀ *ᵥ cvec γ) n = (γ (Fin.last M) - γ n.castSucc) / ((M : ℝ) + 1)) ∧
      ∑ n, cvec γ n = 1 - gbar γ * ((M : ℝ) + 1) / γ (Fin.last M) := by
  let N : ℝ := (M : ℝ) + 1
  have hN : 0 < N := by
    change 0 < (M : ℝ) + 1
    linarith [hM]
  let γN := γ (Fin.last M)
  have hγN : 0 < γN := hγ (Fin.last M)
  -- (7.19): ∑ cₙ = γ̄·∑(1/γⁿ − 1/γᴺ) = γ̄·(∑1/γ − N/γᴺ) = 1 − γ̄·N/γᴺ.
  have h719 : (∑ n, cvec γ n) = 1 - gbar γ * ((M : ℝ) + 1) / γN := by
    rw [lpe_cvec_sum γ hγ, lpe_sum_inner γ hγ, mul_sub]
    linear_combination lpe_gbar_sum γ hγ
  -- (7.18): (Γᵀc)ₙ = γⁿcₙ − (γⁿ−γᴺ)/N·(1 − γ̄N/γᴺ) = (γᴺ−γⁿ)/N.
  have h718 : ∀ n : Fin M, ((Gam γ)ᵀ *ᵥ cvec γ) n = (γN - γ n.castSucc) / N := by
    intro n
    rw [lpe_row_718 γ hγ n, h719]
    simpa [cvec] using lpe_alg_718 (γ n.castSucc) γN (gbar γ) N (hγ n.castSucc) hγN hN
  -- (7.17): v = c + (γ̄/γᴺ)1 = (γ̄/γⁿ); (Γv)ₙ = γ̄ − (γ̄/N)(N − γᴺ/γ̄) = γᴺ/N.
  have h717 : Gam γ *ᵥ (cvec γ + (gbar γ / γN) • (fun _ => (1 : ℝ))) =
      (γN / N) • (fun _ => (1 : ℝ)) := by
    ext n
    have hv : (cvec γ + (gbar γ / γN) • (fun _ => (1 : ℝ))) =
        (fun k : Fin M => gbar γ / γ k.castSucc) := by
      funext k
      simpa using lpe_v_shift γ hγ k
    rw [hv, lpe_row_717 γ hγ n, lpe_sum_one_minus γ hγ]
    simpa using lpe_alg_717 (gbar γ) (∑ n : Fin (M + 1), 1 / γ n) γN N (lpe_gbar_sum γ hγ) hN
  exact ⟨h717, h718, h719⟩
