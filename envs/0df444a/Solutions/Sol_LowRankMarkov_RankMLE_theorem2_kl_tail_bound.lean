-- Prove2me | solution 1 for LowRankMarkov.RankMLE.theorem2_kl_tail_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:41:05.402122+00:00
-- url     : https://prove2.me/submissions/926d1783-6954-4cc7-9ff2-416d1a6e7e5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting
import Theorems.Thm_LowRankMarkov_RankMLE_lemma3_kl_concentration_rank_cone
import Theorems.Thm_LowRankMarkov_RankMLE_ec3_empirical_kl_nonpos
import Theorems.Thm_LowRankMarkov_RankMLE_rank_remark_nuclear_le

open LowRankMarkov.RankMLE CaiCandesShen.Convergence

namespace LRMThm2Aux

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

end LRMThm2Aux

open LRMThm2Aux in
theorem solution :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (p r n : ℕ) (α β : ℝ) (P : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ),
        2 ≤ p → 0 < α → 0 < β →
        IsStochastic P → IsStationary π P → (∀ i, 0 < π i) → IsPrimitive P →
        P.rank = r → Minorated α β P →
        max (20 * Real.log p) (Real.log n) < n * piMax π * (1 - rhoPlus π P) →
        ∀ (est : (Fin (n + 1) → Fin p) → Matrix (Fin p) (Fin p) ℝ),
          (∀ x, IsRankMLE α β r x (est x)) →
          ∀ ξ : ℝ, 0 < ξ →
            trajProb π P (fun x : Fin (n + 1) → Fin p =>
              max (C₁ * r * piMax π * β ^ 2 * p * Real.log p / (piMin π * α ^ 3 * n))
                  (ξ * piMin π / (r * p * piMax π * Real.log p))
                ≤ klDiv π P (est x)) ≤ C₂ * Real.exp (-ξ) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, H⟩ := lemma3_kl_concentration_rank_cone
  refine ⟨4 * C₁, max C₂ 2, by positivity, lt_of_lt_of_le two_pos (le_max_right _ _), ?_⟩
  intro p r n α β P π hp hα hβ hP hπ hπpos hprim hrank hmin hgap est hest ξ hξ
  classical
  have hA1 : Assumption1 α β r P := ⟨hrank, fun j k => Or.inr (hmin j k)⟩
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hr1 : 1 ≤ r := rank_pos_of_stochastic hp P hP.2 hrank
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hmin0 := piMin_pos hp0 π hπpos
  have hmax0 := piMax_pos hp0 π hπpos
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have : 20 * Real.log p ≤ max (20 * Real.log p) (Real.log ((0 : ℕ) : ℝ)) := le_max_left _ _
      simp at hgap
      first | done | linarith
    · exact h0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hπnn : ∀ i, 0 ≤ π i := fun i => (hπpos i).le
  rcases le_or_gt ξ (1 / 2) with hξs | hξl
  · -- small ξ : the bound exceeds one
    refine le_trans (trajProb_le_one π P hπnn hP.1 hπ.2.1 hP.2 _) ?_
    have he : 1 - ξ ≤ Real.exp (-ξ) := by linarith [Real.add_one_le_exp (-ξ)]
    have : (2 : ℝ) * Real.exp (-ξ) ≥ 1 := by linarith
    calc (1 : ℝ) ≤ 2 * Real.exp (-ξ) := this
      _ ≤ max C₂ 2 * Real.exp (-ξ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · set X : ℝ := C₁ * piMax π * β ^ 2 * r * p * Real.log p / (piMin π * α ^ 3 * n) with hX
    have hX0 : 0 < X := by rw [hX]; positivity
    set A : ℝ := 4 * C₁ * r * piMax π * β ^ 2 * p * Real.log p / (piMin π * α ^ 3 * n) with hA
    have hAX : A = 4 * X := by rw [hA, hX]; ring
    set B : ℝ := ξ * piMin π / (r * p * piMax π * Real.log p) with hB
    set η : ℝ := max A B with hη
    have hD : 0 < (r : ℝ) * p * piMax π * Real.log p := by positivity
    have hηlow : piMin π / (2 * piMax π * r * p * Real.log p) < η := by
      refine lt_of_lt_of_le ?_ (le_max_right _ _)
      rw [hB]
      have e : 2 * piMax π * r * p * Real.log p = 2 * (r * p * piMax π * Real.log p) := by ring
      rw [e, div_lt_div_iff₀ (by positivity) hD]
      nlinarith [mul_pos hmin0 hD]
    have Hx := H p r n α β P π hp hα hβ hP hπ hπpos hprim hA1 hgap.le η hηlow
    -- the bad event is contained in the complement of the good event
    have hsub : ∀ x : Fin (n + 1) → Fin p,
        max A B ≤ klDiv π P (est x) →
          ¬ (∀ Q : Matrix (Fin p) (Fin p) ℝ,
              nuclearNorm (Q - P) ≤ 4 * Real.sqrt (2 * (r : ℝ)) * frobNorm (Q - P) →
              (∀ i, ∑ j, Q i j = 1) →
              (∀ i j, α / (p : ℝ) ≤ Q i j ∧ Q i j ≤ β / (p : ℝ)) →
              η ≤ klDiv π P Q →
                |empKL x P Q - klDiv π P Q| ≤ (1 / 2) * klDiv π P Q + X) := by
      intro x hbad hgood
      have hfeas := (hest x).1
      have hcone : nuclearNorm (est x - P) ≤ 4 * Real.sqrt (2 * (r : ℝ)) * frobNorm (est x - P) := by
        have h1 := (rank_remark_nuclear_le P (est x) hrank hfeas.2.2).2
        have hF : 0 ≤ Real.sqrt (2 * (r : ℝ)) * frobNorm (est x - P) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        nlinarith
      have hg := hgood (est x) hcone hfeas.1 hfeas.2.1 hbad
      have hemp := ec3_empirical_kl_nonpos α β hα hβ P hP hrank hmin x (est x) (hest x)
      have hAle : A ≤ klDiv π P (est x) := le_trans (le_max_left _ _) hbad
      have h2 := (abs_le.mp hg).1
      linarith
    calc trajProb π P (fun x => max A B ≤ klDiv π P (est x))
        ≤ trajProb π P (fun x => ¬ (∀ Q : Matrix (Fin p) (Fin p) ℝ,
              nuclearNorm (Q - P) ≤ 4 * Real.sqrt (2 * (r : ℝ)) * frobNorm (Q - P) →
              (∀ i, ∑ j, Q i j = 1) →
              (∀ i j, α / (p : ℝ) ≤ Q i j ∧ Q i j ≤ β / (p : ℝ)) →
              η ≤ klDiv π P Q →
                |empKL x P Q - klDiv π P Q| ≤ (1 / 2) * klDiv π P Q + X)) :=
          trajProb_mono π P hπnn hP.1 _ _ hsub
      _ = 1 - trajProb π P (fun x => ∀ Q : Matrix (Fin p) (Fin p) ℝ,
              nuclearNorm (Q - P) ≤ 4 * Real.sqrt (2 * (r : ℝ)) * frobNorm (Q - P) →
              (∀ i, ∑ j, Q i j = 1) →
              (∀ i j, α / (p : ℝ) ≤ Q i j ∧ Q i j ≤ β / (p : ℝ)) →
              η ≤ klDiv π P Q →
                |empKL x P Q - klDiv π P Q| ≤ (1 / 2) * klDiv π P Q + X) :=
          trajProb_compl π P hπ.2.1 hP.2 _
      _ ≤ C₂ * Real.exp (-(η * piMax π * r * p * Real.log p / piMin π)) := by linarith
      _ ≤ C₂ * Real.exp (-ξ) := by
          apply mul_le_mul_of_nonneg_left _ hC₂.le
          apply Real.exp_le_exp.mpr
          have hBη : B ≤ η := le_max_right _ _
          have : ξ ≤ η * piMax π * r * p * Real.log p / piMin π := by
            rw [le_div_iff₀ hmin0]
            have e : B * (r * p * piMax π * Real.log p) = ξ * piMin π := by
              rw [hB]; field_simp
            have := mul_le_mul_of_nonneg_right hBη hD.le
            nlinarith
          linarith
      _ ≤ max C₂ 2 * Real.exp (-ξ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
