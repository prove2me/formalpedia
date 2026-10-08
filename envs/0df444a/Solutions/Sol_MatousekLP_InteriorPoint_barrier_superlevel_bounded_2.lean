-- Prove2me | solution 2 for MatousekLP.InteriorPoint.barrier_superlevel_bounded
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:14:00.82769+00:00
-- url     : https://prove2.me/submissions/1947b866-91ce-493e-b62a-c0fcac04fbac

import Mathlib
import Definitions.Def_MatousekLP_InteriorPoint_CentralPath

set_option autoImplicit false

open Matrix
namespace MatousekLP.InteriorPoint

lemma log_affine_upper (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    Real.log t ≤ a * t - 1 - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (mul_pos ha ht)
  rw [Real.log_mul ha.ne' ht.ne'] at h
  linarith

lemma barrier_coordinate_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (yt : Fin m → ℝ)
    (hyt : IsDualInterior A c yt) (μ L : ℝ) (hμ : 0 < μ) :
    ∃ U : Fin n → ℝ, ∀ x, IsPrimalInterior A b x → L ≤ barrier c μ x →
      ∀ j, x j ≤ U j := by
  let s := Aᵀ *ᵥ yt - c
  let a := fun j => s j / (2 * μ)
  let K := ∑ j, (-1 - Real.log (a j))
  refine ⟨fun j => (2 * (yt ⬝ᵥ b + μ * K - L)) / s j, ?_⟩
  intro x hx hL j
  have hs : ∀ i, 0 < s i := hyt
  have ha : ∀ i, 0 < a i := fun i => div_pos (hs i) (by positivity)
  have hlog : ∑ i, Real.log (x i) ≤ ∑ i, (a i * x i - 1 - Real.log (a i)) :=
    Finset.sum_le_sum fun i _ => log_affine_upper _ _ (ha i) (hx.2 i)
  have hsum : μ * ∑ i, (a i * x i - 1 - Real.log (a i)) =
      (s ⬝ᵥ x) / 2 + μ * K := by
    simp only [K, dotProduct, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a]
    field_simp
    <;> ring
  have hdual : s ⬝ᵥ x = yt ⬝ᵥ b - c ⬝ᵥ x := by
    dsimp [s]
    rw [sub_dotProduct, dotProduct_comm (Aᵀ *ᵥ yt) x, dotProduct_transpose_mulVec, hx.1]
  have htotal : s ⬝ᵥ x ≤ 2 * (yt ⬝ᵥ b + μ * K - L) := by
    have := mul_le_mul_of_nonneg_left hlog hμ.le
    rw [hsum] at this
    unfold barrier at hL
    linarith
  have hj : s j * x j ≤ s ⬝ᵥ x :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hs i).le (hx.2 i).le) (Finset.mem_univ j)
  apply (le_div_iff₀ (hs j)).2
  nlinarith

end MatousekLP.InteriorPoint

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (xt : Fin n → ℝ)
    (hxt : MatousekLP.InteriorPoint.IsPrimalInterior A b xt) (yt : Fin m → ℝ)
    (hyt : MatousekLP.InteriorPoint.IsDualInterior A c yt) (μ : ℝ) (hμ : 0 < μ) :
    Bornology.IsBounded {x : Fin n → ℝ |
      MatousekLP.InteriorPoint.IsPrimalInterior A b x ∧
      MatousekLP.InteriorPoint.barrier c μ xt ≤ MatousekLP.InteriorPoint.barrier c μ x} := by
  obtain ⟨U, hU⟩ := MatousekLP.InteriorPoint.barrier_coordinate_bound A b c yt hyt μ
    (MatousekLP.InteriorPoint.barrier c μ xt) hμ
  apply (Bornology.IsBounded.pi (fun j => Metric.isBounded_Icc (0 : ℝ) (U j))).subset
  intro x hx
  exact fun j _ => ⟨(hx.1.2 j).le, hU x hx.1 hx.2 j⟩
