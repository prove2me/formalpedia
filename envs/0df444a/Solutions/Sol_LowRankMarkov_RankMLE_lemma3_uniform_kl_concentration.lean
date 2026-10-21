-- Prove2me | solution 1 for LowRankMarkov.RankMLE.lemma3_uniform_kl_concentration
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:41:06.120826+00:00
-- url     : https://prove2.me/submissions/68ff7272-5c9c-4d64-a142-a26d3cbab5ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting
import Theorems.Thm_LowRankMarkov_RankMLE_lemma3_kl_concentration_rank_cone

open LowRankMarkov.RankMLE CaiCandesShen.Convergence

namespace LRMLem3Aux

theorem sum_trajWeight {p : ℕ} (P : Matrix (Fin p) (Fin p) ℝ) (hrow : ∀ i, ∑ j, P i j = 1) :
    ∀ (n : ℕ) (μ : Fin p → ℝ), ∑ x : Fin (n + 1) → Fin p, trajWeight μ P x = ∑ i, μ i := by
  intro n
  induction n with
  | zero => 
    intro μ
    simp only [trajWeight, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin p)) _ _ (fun x => rfl))
  | succ n ih =>
    intro μ
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => Fin p)).sum_comp]
    rw [Fintype.sum_prod_type]
    have hstep : ∀ (a : Fin p) (y : Fin (n + 1) → Fin p),
        trajWeight μ P (Fin.consEquiv (fun _ : Fin (n + 2) => Fin p) (a, y)) =
          μ a * P a (y 0) * ∏ k : Fin n, P (y k.castSucc) (y k.succ) := by
      intro a y
      simp only [trajWeight, Fin.consEquiv_apply, Fin.cons_zero]
      rw [Fin.prod_univ_succ]
      simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one,
        ← Fin.succ_castSucc, Fin.cons_succ]
      ring
    simp_rw [hstep]
    rw [Finset.sum_comm]
    have : ∀ y : Fin (n + 1) → Fin p,
        ∑ a, μ a * P a (y 0) * ∏ k : Fin n, P (y k.castSucc) (y k.succ) =
          trajWeight (fun j => ∑ a, μ a * P a j) P y := by
      intro y
      simp only [trajWeight, Finset.sum_mul]
    simp_rw [this]
    rw [ih]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.mul_sum, hrow, mul_one]

theorem trajWeight_nonneg {p n : ℕ} (π : Fin p → ℝ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hP : ∀ i j, 0 ≤ P i j) (x : Fin (n + 1) → Fin p) :
    0 ≤ trajWeight π P x :=
  mul_nonneg (hπ _) (Finset.prod_nonneg fun k _ => hP _ _)

theorem trajProb_mono {p n : ℕ} (π : Fin p → ℝ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hP : ∀ i j, 0 ≤ P i j)
    (E F : (Fin (n + 1) → Fin p) → Prop) (hEF : ∀ x, E x → F x) :
    trajProb π P E ≤ trajProb π P F := by
  classical
  unfold trajProb
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hE : E x
  · rw [if_pos hE, if_pos (hEF x hE)]
  · rw [if_neg hE]; split_ifs
    · exact trajWeight_nonneg π P hπ hP x
    · exact le_rfl

theorem trajProb_compl {p n : ℕ} (π : Fin p → ℝ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hsum : ∑ i, π i = 1) (hrow : ∀ i, ∑ j, P i j = 1)
    (E : (Fin (n + 1) → Fin p) → Prop) :
    trajProb π P (fun x => ¬ E x) = 1 - trajProb π P E := by
  classical
  have htot := sum_trajWeight P hrow n π
  rw [hsum] at htot
  rw [← htot]
  unfold trajProb
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hE : E x <;> simp [hE]

theorem trajProb_le_one {p n : ℕ} (π : Fin p → ℝ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hP : ∀ i j, 0 ≤ P i j)
    (hsum : ∑ i, π i = 1) (hrow : ∀ i, ∑ j, P i j = 1)
    (E : (Fin (n + 1) → Fin p) → Prop) :
    trajProb π P E ≤ 1 := by
  classical
  have h1 := trajProb_compl π P hsum hrow E
  have h2 : 0 ≤ trajProb π P (fun x => ¬ E x) := by
    unfold trajProb
    exact Finset.sum_nonneg fun x _ => by split_ifs; exacts [trajWeight_nonneg π P hπ hP x, le_rfl]
  linarith


theorem rank_pos_of_stochastic {p r : ℕ} (hp : 2 ≤ p) (P : Matrix (Fin p) (Fin p) ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1) (hrank : P.rank = r) : 1 ≤ r := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · exfalso
    subst h0
    have hbot : LinearMap.range P.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hrank
    have hmem : P.mulVecLin (fun _ => (1 : ℝ)) ∈ LinearMap.range P.mulVecLin := ⟨_, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    have := congrFun hmem ⟨0, by omega⟩
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hrow] at this
  · exact h0

theorem piMin_pos {p : ℕ} (hp : 0 < p) (π : Fin p → ℝ) (hπ : ∀ i, 0 < π i) : 0 < piMin π := by
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := π)
  unfold piMin; rw [← hi₀]; exact hπ i₀

theorem piMax_pos {p : ℕ} (hp : 0 < p) (π : Fin p → ℝ) (hπ : ∀ i, 0 < π i) : 0 < piMax π :=
  lt_of_lt_of_le (hπ ⟨0, hp⟩) (le_ciSup (Finite.bddAbove_range π) _)

end LRMLem3Aux

open LRMLem3Aux in
theorem solution :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (p r n : ℕ) (α β : ℝ) (P : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ),
        2 ≤ p → 0 < α → 0 < β →
        IsStochastic P → IsStationary π P → (∀ i, 0 < π i) → IsPrimitive P →
        Assumption1 α β r P →
        max (20 * Real.log p) (Real.log n) ≤ n * piMax π * (1 - rhoPlus π P) →
        ∀ η : ℝ, piMin π / (2 * piMax π * r * p * Real.log p) < η →
          1 - C₂ * Real.exp (-(η * piMax π * r * p * Real.log p / piMin π)) ≤
            trajProb π P (fun x : Fin (n + 1) → Fin p => ∀ Q : Matrix (Fin p) (Fin p) ℝ,
              ConcentrationClass α β P Q → η ≤ klDiv π P Q →
                |empKL x P Q - klDiv π P Q| ≤
                  (1 / 2) * klDiv π P Q +
                    C₁ * piMax π * β ^ 2 * r * p * Real.log p / (piMin π * α ^ 3 * n)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, H⟩ := lemma3_kl_concentration_rank_cone
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro p r n α β P π hp hα hβ hP hπ hπpos hprim hA1 hgap η hη
  have hr1 : 1 ≤ r := rank_pos_of_stochastic hp P hP.2 hA1.1
  refine le_trans (H p r n α β P π hp hα hβ hP hπ hπpos hprim hA1 hgap η hη) ?_
  refine trajProb_mono π P (fun i => (hπpos i).le) hP.1 _ _ ?_
  intro x hx Q hQ hηQ
  refine hx Q ?_ hQ.2.1 hQ.2.2 hηQ
  have hs : Real.sqrt 2 ≤ Real.sqrt (2 * (r : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    linarith
  have hF : 0 ≤ frobNorm (Q - P) := Real.sqrt_nonneg _
  calc nuclearNorm (Q - P) ≤ 4 * Real.sqrt 2 * frobNorm (Q - P) := hQ.1
    _ ≤ 4 * Real.sqrt (2 * (r : ℝ)) * frobNorm (Q - P) := by gcongr
