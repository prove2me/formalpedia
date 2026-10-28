-- Prove2me | solution 1 for NetInspect.Rate.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-28T06:21:28.914783+00:00
-- url     : https://prove2.me/submissions/a68f6fc6-970a-4957-a80f-50d7abf06d0e

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_NetInspect_Rate_Model
import Mathlib.Algebra.Ring.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.Birkhoff
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases


-- Auxiliary proofs copied from the platform-accepted proof of lemma_EC_3.
-- Snapshot: verification/platform/NetInspect.Rate.lemma_EC_3-accepted.lean.
namespace Aux_NetInspect_Rate_lemma_EC_3
open Finset NetInspect.Rate Fin.NatCast

variable {α : Type*} [Fintype α] [DecidableEq α] {n b : ℕ}

theorem np20261028_cast_inj [NeZero n] {i1 i2 : ℕ} (h1 : i1 < n) (h2 : i2 < n)
    (h : ((i1 : Fin n)) = (i2 : Fin n)) : i1 = i2 := by
  have := congrArg Fin.val h
  rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

theorem np20261028_win_eq [NeZero n] (x : Fin n → α) (k : Fin n) :
    window x b k = (range b).image (fun i : ℕ => x (k + (i : Fin n))) := by
  unfold window
  apply Finset.image_congr
  intro i _
  show x _ = x _
  congr 1
  ext
  rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]

theorem np20261028_win_card [NeZero n] (x : Fin n → α) (hx : Function.Injective x) (hbn : b ≤ n)
    (k : Fin n) : (window x b k).card = b := by
  rw [np20261028_win_eq, card_image_of_injOn, card_range]
  intro i1 h1 i2 h2 heq
  have h1' : i1 < b := mem_range.mp h1
  have h2' : i2 < b := mem_range.mp h2
  have := add_left_cancel (hx heq)
  exact np20261028_cast_inj (by omega) (by omega) this

theorem np20261028_win_count [NeZero n] (x : Fin n → α) (hx : Function.Injective x) (hbn : b ≤ n)
    (j : Fin n) : (univ.filter fun k : Fin n => x j ∈ window x b k).card = b := by
  have hset : (univ.filter fun k : Fin n => x j ∈ window x b k) =
      (range b).image (fun i : ℕ => j - (i : Fin n)) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, np20261028_win_eq, mem_image]
    constructor
    · rintro ⟨i, hi, hk⟩
      exact ⟨i, hi, by rw [← hx hk]; abel⟩
    · rintro ⟨i, hi, hk⟩
      exact ⟨i, hi, by rw [← hk]; congr 1; abel⟩
  rw [hset, card_image_of_injOn, card_range]
  intro i1 h1 i2 h2 heq
  have h1' : i1 < b := mem_range.mp h1
  have h2' : i2 < b := mem_range.mp h2
  have : ((i1 : Fin n)) = (i2 : Fin n) := sub_right_injective heq
  exact np20261028_cast_inj (by omega) (by omega) this

theorem np20261028_fiber_sum (x : Fin n → α) (P : Finset α → Prop) [DecidablePred P] :
    ∑ X : Act α b, (if P X.1 then (((univ.filter fun k => window x b k = X.1).card : ℕ) : ℝ) else 0)
      = ((univ.filter fun k => P (window x b k)).card : ℝ) := by
  rw [card_eq_sum_card_fiberwise (f := fun k => (⟨window x b k, window_card_le x b k⟩ : Act α b))
    (t := univ) (fun _ _ => mem_coe.mpr (mem_univ _))]
  push_cast
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs with hP
  · congr 2
    ext k
    simp only [mem_filter, mem_univ, true_and, Subtype.ext_iff]
    constructor
    · intro h; exact ⟨h ▸ hP, h⟩
    · intro h; exact h.2
  · symm
    norm_cast
    rw [card_eq_zero, filter_eq_empty_iff]
    intro k hk hfk
    simp only [mem_filter, mem_univ, true_and] at hk
    apply hP
    rw [← hfk]; exact hk

theorem np20261028_mixed (x : Fin n → α) (hn : 0 < n) : BlottoLP.Flow.IsMixed (cycStrat x b) := by
  refine ⟨fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  unfold cycStrat
  rw [← Finset.sum_div]
  have := np20261028_fiber_sum (b := b) x (fun _ => True)
  have hu : (univ.filter fun _ : Fin n => True) = univ := by ext; simp
  simp only [if_true] at this
  rw [this, hu, card_univ, Fintype.card_fin, div_self]
  exact_mod_cast hn.ne'

theorem np20261028_margv [NeZero n] (x : Fin n → α) (hx : Function.Injective x) (hbn : b ≤ n) (j : Fin n) :
    marg (cycStrat x b) (x j) = (b : ℝ) / (n : ℝ) := by
  unfold marg cycStrat
  have h := np20261028_fiber_sum (b := b) x (fun X => x j ∈ X)
  rw [np20261028_win_count x hx hbn] at h
  rw [← h, Finset.sum_div]
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs <;> simp

end Aux_NetInspect_Rate_lemma_EC_3




namespace NetInspect.Rate
open Finset DetectionModel
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem np20261028_packing_sizes_nonempty (G : DetectionModel V E) :
    {k : ℕ | ∃ T : Finset E, T.card = k ∧ G.IsSetPacking T}.Nonempty := by
  refine ⟨0, ∅, rfl, ?_⟩
  intro i
  simp [F]

theorem np20261028_packing_sizes_bddAbove (G : DetectionModel V E) :
    BddAbove {k : ℕ | ∃ T : Finset E, T.card = k ∧ G.IsSetPacking T} := by
  refine ⟨Fintype.card E, ?_⟩
  rintro k ⟨T, rfl, _⟩
  exact card_le_univ T

theorem np20261028_exists_max_packing (G : DetectionModel V E) :
    ∃ T : Finset E, T.card = G.mStar ∧ G.IsSetPacking T :=
  Nat.sSup_mem (np20261028_packing_sizes_nonempty G) (np20261028_packing_sizes_bddAbove G)

theorem np20261028_mStar_le_card_packing (G : DetectionModel V E) : G.mStar ≤ Fintype.card E := by
  obtain ⟨T, ht, _⟩ := np20261028_exists_max_packing G
  rw [← ht]
  exact card_le_univ T

theorem np20261028_one_le_mStar_of_nonempty (G : DetectionModel V E) [Nonempty E] : 1 ≤ G.mStar := by
  classical
  obtain ⟨e⟩ := ‹Nonempty E›
  apply le_csSup (np20261028_packing_sizes_bddAbove G)
  refine ⟨{e}, by simp, ?_⟩
  intro i
  unfold F
  exact (card_le_card inter_subset_right).trans (by simp)

theorem np20261028_F_le_card_of_packing (G : DetectionModel V E) (S : Finset V) (T : Finset E)
    (hT : G.IsSetPacking T) : G.F S T ≤ S.card := by
  classical
  have heq : G.CS S ∩ T = S.biUnion (fun i => G.C i ∩ T) := by
    ext e
    simp only [CS, mem_inter, mem_biUnion]
    constructor
    · rintro ⟨⟨i, hi, hie⟩, he⟩
      exact ⟨i, hi, hie, he⟩
    · rintro ⟨i, hi, hie, he⟩
      exact ⟨⟨i, hi, hie⟩, he⟩
  unfold F
  rw [heq]
  calc
    _ ≤ ∑ i ∈ S, (G.C i ∩ T).card := card_biUnion_le
    _ ≤ ∑ _i ∈ S, 1 := by
      apply sum_le_sum
      intro i _
      simpa [F, CS] using hT i
    _ = S.card := by simp

end NetInspect.Rate



namespace NetInspect.Rate
open Finset

/-- The sum of attack marginals is the expected number of attacked components. -/
theorem np20261028_sum_marg_eq_expected_card {E : Type*} [Fintype E] [DecidableEq E]
    {b : ℕ} (σ : Act E b → ℝ) :
    ∑ e, marg σ e = ∑ T, σ T * (T.1.card : ℝ) := by
  unfold marg
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp [Finset.sum_ite_mem, mul_comm]

/-- Every np20261028_mixed strategy over plans of size at most b has total marginal mass at most b. -/
theorem np20261028_sum_marg_le_budget {E : Type*} [Fintype E] [DecidableEq E]
    {b : ℕ} (σ : Act E b → ℝ) (hσ : BlottoLP.Flow.IsMixed σ) :
    ∑ e, marg σ e ≤ (b : ℝ) := by
  rw [np20261028_sum_marg_eq_expected_card]
  calc
    _ ≤ ∑ T : Act E b, σ T * (b : ℝ) := by
      apply Finset.sum_le_sum
      intro T _
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast T.2) (hσ.1 T)
    _ = (b : ℝ) := by rw [← Finset.sum_mul, hσ.2, one_mul]

end NetInspect.Rate



namespace NetInspect.Rate
open Finset DetectionModel

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem np20261028_undet_eq_sum (G : DetectionModel V E) (S : Finset V) (T : Finset E) :
    G.undet S T = ∑ e ∈ T, if e ∈ G.CS S then (0 : ℝ) else 1 := by
  classical
  have hc : ∑ e ∈ T, (if e ∈ G.CS S then (1 : ℝ) else 0) = (G.F S T : ℝ) := by
    simp [F, sum_ite, filter_mem_eq_inter, inter_comm]
  calc
    G.undet S T = (∑ _e ∈ T, (1 : ℝ)) -
        ∑ e ∈ T, (if e ∈ G.CS S then (1 : ℝ) else 0) := by simp [undet, hc]
    _ = ∑ e ∈ T, (1 - if e ∈ G.CS S then (1 : ℝ) else 0) := by rw [sum_sub_distrib]
    _ = _ := by apply sum_congr rfl; intro e _; split_ifs <;> norm_num

namespace DetectionModel
/-- Weighted probability that a component escapes inspection. No normalization assumption needed. -/
def np20261028_missProb {b1 : ℕ} (G : DetectionModel V E) (σ1 : Act V b1 → ℝ) (e : E) : ℝ :=
  ∑ S, σ1 S * (if e ∈ G.CS S.1 then 0 else 1)
end DetectionModel

theorem np20261028_U_eq_sum_marg {b1 b2 : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) :
    G.U σ1 σ2 = ∑ e, marg σ2 e * G.np20261028_missProb σ1 e := by
  classical
  have hu (S : Finset V) (T : Finset E) : G.undet S T =
      ∑ e, if e ∈ T then (if e ∈ G.CS S then (0 : ℝ) else 1) else 0 := by
    rw [np20261028_undet_eq_sum]
    simp
  unfold U BlottoLP.Flow.expPay payoff
  simp_rw [hu, mul_sum]
  calc
    _ = ∑ T : Act E b2, ∑ e : E, ∑ S : Act V b1,
        σ2 T * σ1 S * (if e ∈ T.1 then (if e ∈ G.CS S.1 then (0 : ℝ) else 1) else 0) := by
      apply sum_congr rfl
      intro T _
      rw [sum_comm]
    _ = ∑ e : E, ∑ T : Act E b2, ∑ S : Act V b1,
        σ2 T * σ1 S * (if e ∈ T.1 then (if e ∈ G.CS S.1 then (0 : ℝ) else 1) else 0) := sum_comm
    _ = _ := by
      unfold marg np20261028_missProb
      simp_rw [sum_mul, mul_sum]
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro T _
      apply sum_congr rfl
      intro S _
      by_cases he : e ∈ T.1 <;> simp [he, mul_assoc]

theorem np20261028_U_eq_of_marg_eq {b1 b2 b2' : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (τ2 : Act E b2' → ℝ)
    (h : ∀ e, marg σ2 e = marg τ2 e) : G.U σ1 σ2 = G.U σ1 τ2 := by
  simp only [np20261028_U_eq_sum_marg, h]

theorem np20261028_U_eq_mul_of_marg_eq_mul {b1 b2 b2' : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (τ2 : Act E b2' → ℝ) (c : ℝ)
    (h : ∀ e, marg σ2 e = c * marg τ2 e) : G.U σ1 σ2 = c * G.U σ1 τ2 := by
  simp only [np20261028_U_eq_sum_marg, h, mul_sum, mul_assoc]

theorem np20261028_missProb_nonneg {b1 : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (hσ : BlottoLP.Flow.IsMixed σ1) (e : E) :
    0 ≤ G.np20261028_missProb σ1 e := by
  unfold DetectionModel.np20261028_missProb
  apply sum_nonneg
  intro S _
  exact mul_nonneg (hσ.1 S) (by split_ifs <;> norm_num)

theorem np20261028_missProb_le_one {b1 : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (hσ : BlottoLP.Flow.IsMixed σ1) (e : E) :
    G.np20261028_missProb σ1 e ≤ 1 := by
  unfold DetectionModel.np20261028_missProb
  calc
    _ ≤ ∑ S, σ1 S := by
      apply sum_le_sum
      intro S _
      split_ifs <;> simp [hσ.1 S]
    _ = 1 := hσ.2

end NetInspect.Rate




namespace NetInspect.Rate
open Finset Matrix

set_option backward.isDefEq.respectTransparency.types false in
theorem np20261028_marginals_doubly_stochastic {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : E → ℝ) (B : Finset E) (hB : B.Nonempty) (hBc : Bᶜ.Nonempty)
    (hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1) (hs : ∑ e, ρ e = (B.card : ℝ)) :
    ((fun i j => if i ∈ B then ρ j / B.card else (1 - ρ j) / Bᶜ.card) : Matrix E E ℝ) ∈
      doublyStochastic ℝ E := by
  have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hc : (Bᶜ.card : ℝ) ≠ 0 := by exact_mod_cast hBc.card_pos.ne'
  refine (mem_doublyStochastic_iff_sum (M :=
    (fun i j => if i ∈ B then ρ j / B.card else (1 - ρ j) / Bᶜ.card : Matrix E E ℝ))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    split_ifs <;> exact div_nonneg (by linarith [(hρ j).1, (hρ j).2]) (Nat.cast_nonneg _)
  · intro i
    by_cases hi : i ∈ B
    · simp [hi, ← sum_div, hs, hb]
    · simp only [hi, ↓reduceIte, ← sum_div, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, hs]
      have hcard : (Fintype.card E : ℝ) - B.card = (Bᶜ.card : ℝ) := by
        have hh : (B.card : ℝ) + Bᶜ.card = Fintype.card E := by
          exact_mod_cast Finset.card_add_card_compl B
        linarith
      rw [hcard, div_self hc]
  · intro j
    rw [sum_ite]
    simp only [filter_mem_eq_inter, univ_inter]
    have hfilter : (univ.filter fun i => i ∉ B) = Bᶜ := by ext i; simp
    rw [hfilter]
    simp only [sum_const, nsmul_eq_mul]
    field_simp [hb, hc]
    <;> ring
theorem np20261028_realize_from_finite_family {E K : Type*} [Fintype E] [DecidableEq E]
    [Fintype K] {b : ℕ} (A : K → Act E b) (w : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    ∃ σ : Act E b → ℝ, BlottoLP.Flow.IsMixed σ ∧
      ∀ e, marg σ e = ∑ k, if e ∈ (A k).1 then w k else 0 := by
  classical
  let σ : Act E b → ℝ := fun T => ∑ k, if A k = T then w k else 0
  refine ⟨σ, ⟨?_, ?_⟩, ?_⟩
  · intro T
    exact sum_nonneg fun k _ => by split_ifs <;> simp_all
  · dsimp [σ]
    rw [sum_comm]
    simpa using hs
  · intro e
    unfold marg
    dsimp [σ]
    simp_rw [Finset.ite_sum_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    by_cases he : e ∈ (A k).1
    · simp only [he, ↓reduceIte]
      rw [sum_eq_single (A k)]
      · simp [he]
      · intro T _ hT
        by_cases ht : e ∈ T.1 <;> simp [ht, Ne.symm hT]
      · simp
    · simp only [he, ↓reduceIte]
      apply sum_eq_zero
      intro T _
      by_cases ht : e ∈ T.1
      · have hn : A k ≠ T := by intro h; exact he (h ▸ ht)
        simp [ht, hn]
      · simp [ht]

theorem np20261028_sum_permMatrix_subset {E : Type*} [Fintype E] [DecidableEq E]
    (B : Finset E) (π : Equiv.Perm E) (e : E) :
    ∑ i ∈ B, π.permMatrix ℝ i e = if e ∈ B.image π then 1 else 0 := by
  classical
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  by_cases he : π.symm e ∈ B
  · rw [sum_eq_single (π.symm e)]
    · simp [mem_image, he, Equiv.apply_eq_iff_eq_symm_apply]
    · intro i hi hn
      simp [show π i ≠ e by intro h; exact hn (π.injective (by simpa using h))]
    · simp [he]
  · have he' : e ∉ B.image π := by
      rintro he'
      obtain ⟨i, hi, hie⟩ := mem_image.mp he'
      exact he (by simpa [← hie] using hi)
    rw [if_neg he']
    apply sum_eq_zero
    intro i hi
    have hn : π i ≠ e := by intro h; exact he (by simpa [← h] using hi)
    simp [hn]
theorem np20261028_realize_marginals_of_subset {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : E → ℝ) (B : Finset E) (hB : B.Nonempty) (hBc : Bᶜ.Nonempty)
    (hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1) (hs : ∑ e, ρ e = (B.card : ℝ)) :
    ∃ σ : Act E B.card → ℝ, BlottoLP.Flow.IsMixed σ ∧ ∀ e, marg σ e = ρ e := by
  classical
  let M : Matrix E E ℝ := fun i j =>
    if i ∈ B then ρ j / B.card else (1 - ρ j) / Bᶜ.card
  obtain ⟨w, hw, hw1, hM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (np20261028_marginals_doubly_stochastic ρ B hB hBc hρ hs)
  let A : Equiv.Perm E → Act E B.card := fun π =>
    ⟨B.image π, by rw [card_image_of_injective _ π.injective]⟩
  obtain ⟨σ, hσ, hm⟩ := np20261028_realize_from_finite_family A w hw hw1
  refine ⟨σ, hσ, fun e => ?_⟩
  rw [hm]
  change (∑ π : Equiv.Perm E, if e ∈ B.image π then w π else 0) = ρ e
  calc
    _ = ∑ π : Equiv.Perm E, w π * ∑ i ∈ B, π.permMatrix ℝ i e := by
      apply sum_congr rfl
      intro π _
      rw [np20261028_sum_permMatrix_subset]
      split_ifs <;> simp
    _ = ∑ i ∈ B, M i e := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      have hij := congrArg (fun X : Matrix E E ℝ => X i e) hM
      simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, M] using hij
    _ = ρ e := by
      have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
      calc
        _ = ∑ _i ∈ B, ρ e / (B.card : ℝ) := by
          apply sum_congr rfl
          intro i hi
          simp [M, hi]
        _ = ρ e := by simp only [sum_const, nsmul_eq_mul]; field_simp
theorem np20261028_realize_marginals {E : Type*} [Fintype E] [DecidableEq E]
    (b : ℕ) (ρ : E → ℝ) (hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1)
    (hs : ∑ e, ρ e = (b : ℝ)) :
    ∃ σ : Act E b → ℝ, BlottoLP.Flow.IsMixed σ ∧ ∀ e, marg σ e = ρ e := by
  classical
  have hb : b ≤ Fintype.card E := by
    have hh : (b : ℝ) ≤ Fintype.card E := by
      rw [← hs]
      calc
        _ ≤ ∑ _ : E, (1 : ℝ) := sum_le_sum fun e _ => (hρ e).2
        _ = _ := by simp
    exact_mod_cast hh
  by_cases hz : b = 0
  · subst b
    have hr : ∀ e, ρ e = 0 := by
      have hs0 : ∑ e, ρ e = 0 := by simpa using hs
      have hh := (sum_eq_zero_iff_of_nonneg (s := univ) (fun e _ => (hρ e).1)).1 hs0
      exact fun e => hh e (mem_univ e)
    obtain ⟨σ, hσ, hm⟩ := np20261028_realize_from_finite_family
      (fun _ : Unit => (⟨∅, by simp⟩ : Act E 0)) (fun _ => (1 : ℝ)) (by simp) (by simp)
    refine ⟨σ, hσ, fun e => ?_⟩
    simpa [hr e] using hm e
  by_cases hn : b = Fintype.card E
  · have hr : ∀ e, ρ e = 1 := by
      have hh : ∑ e, (1 - ρ e) = 0 := by simp [sum_sub_distrib, hs, hn]
      have hh' := (sum_eq_zero_iff_of_nonneg
        (fun e _ => sub_nonneg.mpr (hρ e).2)).1 hh
      intro e
      have := hh' e (mem_univ e)
      linarith
    obtain ⟨σ, hσ, hm⟩ := np20261028_realize_from_finite_family
      (fun _ : Unit => (⟨univ, by simp [hn]⟩ : Act E b))
      (fun _ => (1 : ℝ)) (by simp) (by simp)
    refine ⟨σ, hσ, fun e => ?_⟩
    simpa [hr e] using hm e
  obtain ⟨B, _, hB⟩ := exists_subset_card_eq (s := (univ : Finset E)) (by simpa using hb)
  have hne : B.Nonempty := card_pos.mp (by omega)
  have hcne : Bᶜ.Nonempty := card_pos.mp (by rw [card_compl, hB]; omega)
  subst b
  exact np20261028_realize_marginals_of_subset ρ B hne hcne hρ hs

theorem np20261028_lemma_EC_4 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b2 : ℕ} (hb2 : b2 < G.mStar) (ρ : E → ℝ) (hρ : ∀ e : E, 0 ≤ ρ e ∧ ρ e ≤ 1)
    (hsum : ∑ e : E, ρ e = (b2 : ℝ)) :
    ∃ σ2 : Act E b2 → ℝ, BlottoLP.Flow.IsMixed σ2 ∧ ∀ e : E, marg σ2 e = ρ e :=
  np20261028_realize_marginals b2 ρ hρ hsum

end NetInspect.Rate




namespace BlottoLP.Flow
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

lemma np20261028_expPay_affine_left (M : α → β → ℝ) (σ σ' : α → ℝ) (τ : β → ℝ) (a b : ℝ) :
    expPay M (a • σ + b • σ') τ = a * expPay M σ τ + b * expPay M σ' τ := by
  simp only [expPay, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

lemma np20261028_expPay_affine_right (M : α → β → ℝ) (σ : α → ℝ) (τ τ' : β → ℝ) (a b : ℝ) :
    expPay M σ (a • τ + b • τ') = a * expPay M σ τ + b * expPay M σ τ' := by
  simp only [expPay, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Every finite nonempty real zero-sum game has a np20261028_mixed Nash equilibrium. -/
theorem np20261028_exists_isNashEq [Nonempty α] [Nonempty β] (M : α → β → ℝ) :
    ∃ σ τ, IsNashEq M σ τ := by
  classical
  have hcontσ (τ : β → ℝ) : Continuous (fun σ => expPay M σ τ) := by
    unfold expPay
    fun_prop
  have hcontτ (σ : α → ℝ) : Continuous (fun τ => expPay M σ τ) := by
    unfold expPay
    fun_prop
  have hconv (σ : α → ℝ) : ConvexOn ℝ (stdSimplex ℝ β) (fun τ => expPay M σ τ) := by
    refine ⟨convex_stdSimplex _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (np20261028_expPay_affine_right M σ x y a b).le
  have hconc (τ : β → ℝ) : ConcaveOn ℝ (stdSimplex ℝ α) (fun σ => expPay M σ τ) := by
    refine ⟨convex_stdSimplex _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (np20261028_expPay_affine_left M x y τ a b).ge
  obtain ⟨τ, hτ, σ, hσ, hs⟩ := Sion.exists_isSaddlePointOn
    (f := fun τ σ => expPay M σ τ)
    ⟨_, single_mem_stdSimplex ℝ (Classical.choice inferInstance : β)⟩
    (convex_stdSimplex ℝ β) (isCompact_stdSimplex ℝ β)
    (fun σ _ => (hcontτ σ).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun σ _ => (hconv σ).quasiconvexOn)
    (convex_stdSimplex ℝ α)
    ⟨_, single_mem_stdSimplex ℝ (Classical.choice inferInstance : α)⟩
    (isCompact_stdSimplex ℝ α)
    (fun τ _ => (hcontσ τ).upperSemicontinuous.upperSemicontinuousOn _)
    (fun τ _ => (hconc τ).quasiconcaveOn)
  refine ⟨σ, τ, hσ, hτ, ?_, ?_⟩
  · intro σ' hσ'
    exact hs τ hτ σ' hσ'
  · intro τ' hτ'
    exact hs τ' hτ' σ hσ

 theorem IsNashEq.np20261028_expPay_eq {M : α → β → ℝ} {σ σ' : α → ℝ} {τ τ' : β → ℝ}
    (h : IsNashEq M σ τ) (h' : IsNashEq M σ' τ') :
    expPay M σ τ = expPay M σ' τ' := by
  apply le_antisymm
  · exact (h.2.2.2 τ' h'.2.1).trans (h'.2.2.1 σ h.1)
  · exact (h'.2.2.2 τ h.2.1).trans (h.2.2.1 σ' h'.1)

 theorem IsNashEq.np20261028_cross {M : α → β → ℝ} {σ σ' : α → ℝ} {τ τ' : β → ℝ}
    (h : IsNashEq M σ τ) (h' : IsNashEq M σ' τ') : IsNashEq M σ τ' := by
  have hv := h.np20261028_expPay_eq h'
  have hx : expPay M σ τ' = expPay M σ τ := by
    apply le_antisymm
    · exact (h'.2.2.1 σ h.1).trans hv.ge
    · exact h.2.2.2 τ' h'.2.1
  refine ⟨h.1, h'.2.1, ?_, ?_⟩
  · intro ρ hρ
    rw [hx, hv]
    exact h'.2.2.1 ρ hρ
  · intro ρ hρ
    rw [hx]
    exact h.2.2.2 ρ hρ

lemma np20261028_expPay_eq_sum_pure_left [DecidableEq α] (M : α → β → ℝ) (σ : α → ℝ) (τ : β → ℝ) :
    expPay M σ τ = ∑ a, σ a * expPay M (pureMixed a) τ := by
  simp only [expPay, pureMixed]
  simp [Finset.mul_sum, mul_assoc]

lemma np20261028_expPay_eq_sum_pure_right [DecidableEq β] (M : α → β → ℝ) (σ : α → ℝ) (τ : β → ℝ) :
    expPay M σ τ = ∑ b, τ b * expPay M σ (pureMixed b) := by
  simp only [expPay, pureMixed]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma np20261028_expPay_le_of_pure_left [DecidableEq α] (M : α → β → ℝ) {σ : α → ℝ}
    (hσ : IsMixed σ) (τ : β → ℝ) (v : ℝ)
    (h : ∀ a, expPay M (pureMixed a) τ ≤ v) : expPay M σ τ ≤ v := by
  rw [np20261028_expPay_eq_sum_pure_left]
  calc
    _ ≤ ∑ a, σ a * v := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hσ.1 a)
    _ = v := by rw [← Finset.sum_mul, hσ.2, one_mul]

lemma np20261028_le_expPay_of_pure_right [DecidableEq β] (M : α → β → ℝ) (σ : α → ℝ)
    {τ : β → ℝ} (hτ : IsMixed τ) (v : ℝ)
    (h : ∀ b, v ≤ expPay M σ (pureMixed b)) : v ≤ expPay M σ τ := by
  rw [np20261028_expPay_eq_sum_pure_right]
  calc
    v = ∑ b, τ b * v := by rw [← Finset.sum_mul, hτ.2, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h b) (hτ.1 b)

end BlottoLP.Flow




namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The exact conclusion of the network detection-rate theorem. -/
def np20261028_DetectionRateConclusion (G : DetectionModel V E) (b1 : ℕ) : Prop :=
    (∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 → G.rate σ1 σ2 = r) ∧
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E 1 → ℝ), G.IsNE b1 1 σ1 σ2 →
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∃ σ2' : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2')

 theorem np20261028_theorem_2_vacuous (G : DetectionModel V E) (b1 : ℕ) (hm : G.mStar ≤ 1) :
    np20261028_DetectionRateConclusion G b1 := by
  refine ⟨⟨0, le_rfl, zero_le_one, ?_⟩, ?_⟩
  · intro b2 hb hm'
    omega
  · intro σ1 σ2 hne b2 hb hm'
    omega

 lemma np20261028_mStar_le_card (G : DetectionModel V E) : G.mStar ≤ Fintype.card E := by
  apply csSup_le
  · exact ⟨0, ∅, by simp, by simp [IsSetPacking, F]⟩
  · rintro k ⟨T, rfl, hT⟩
    exact Finset.card_le_univ T

 lemma np20261028_act_zero_eq_empty (S : Act V 0) : S.1 = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero S.2)

 lemma np20261028_mixed_zero_unique {σ τ : Act V 0 → ℝ} (hσ : IsMixed σ) (hτ : IsMixed τ) : σ = τ := by
  classical
  letI : Subsingleton (Act V 0) := ⟨fun S T => Subtype.ext ((np20261028_act_zero_eq_empty S).trans (np20261028_act_zero_eq_empty T).symm)⟩
  letI : Nonempty (Act V 0) := ⟨⟨∅, by simp⟩⟩
  funext S
  have hs : σ S = 1 := by
    have he : ∑ a, σ a = σ S := Finset.sum_eq_single S
      (fun a _ ha => False.elim (ha (Subsingleton.elim a S))) (by simp)
    exact he.symm.trans hσ.2
  have ht : τ S = 1 := by
    have he : ∑ a, τ a = τ S := Finset.sum_eq_single S
      (fun a _ ha => False.elim (ha (Subsingleton.elim a S))) (by simp)
    exact he.symm.trans hτ.2
  exact hs.trans ht.symm

 lemma np20261028_zero_budget_payoff (G : DetectionModel V E) {b2 : ℕ}
    (T : Act E b2) (S : Act V 0) : G.payoff 0 b2 T S = T.1.card := by
  simp [payoff, undet, F, CS, np20261028_act_zero_eq_empty S]

 theorem np20261028_zero_budget_rate (G : DetectionModel V E) {b2 : ℕ} (hb : 1 ≤ b2)
    (hcard : b2 ≤ Fintype.card E) (σ1 : Act V 0 → ℝ) (σ2 : Act E b2 → ℝ)
    (hne : G.IsNE 0 b2 σ1 σ2) : G.rate σ1 σ2 = 0 := by
  classical
  have hp (τ : Act E b2 → ℝ) : expPay (G.payoff 0 b2) τ σ1 = ∑ T, τ T * (T.1.card : ℝ) := by
    unfold expPay
    apply sum_congr rfl
    intro T _
    simp_rw [np20261028_zero_budget_payoff]
    calc
      _ = (τ T * (T.1.card : ℝ)) * ∑ S, σ1 S := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        ring
      _ = _ := by rw [hne.2.1.2, mul_one]
  obtain ⟨T, hTu, hTc⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset E)) hcard
  let t : Act E b2 := ⟨T, hTc.le⟩
  have ht : IsMixed (pureMixed t) := by
    constructor
    · intro a
      simp only [pureMixed]
      split_ifs <;> norm_num
    · simp [pureMixed]
  have hlo := hne.2.2.1 (pureMixed t) ht
  rw [hp, hp] at hlo
  have hpure : (∑ T : Act E b2, pureMixed t T * (T.1.card : ℝ)) = b2 := by
    simp [pureMixed, t, hTc]
  rw [hpure] at hlo
  have hsum : ∑ T : Act E b2, σ2 T * ((b2 : ℝ) - T.1.card) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hne.1.2, one_mul]
    have hhi : (∑ T : Act E b2, σ2 T * (T.1.card : ℝ)) ≤ b2 := by
      calc
        _ ≤ ∑ T : Act E b2, σ2 T * b2 := Finset.sum_le_sum fun T _ =>
          mul_le_mul_of_nonneg_left (by exact_mod_cast T.2) (hne.1.1 T)
        _ = b2 := by rw [← Finset.sum_mul, hne.1.2, one_mul]
    linarith
  have hnneg (T : Act E b2) : 0 ≤ σ2 T * ((b2 : ℝ) - T.1.card) :=
    mul_nonneg (hne.1.1 T) (sub_nonneg.mpr (by exact_mod_cast T.2))
  let emptyAct : Act E b2 := ⟨∅, by simp⟩
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun T _ => hnneg T).mp hsum emptyAct (mem_univ _)
  have he : σ2 emptyAct = 0 := by
    have hbR : (0 : ℝ) < b2 := by exact_mod_cast (show 0 < b2 by omega)
    simp only [emptyAct, card_empty, Nat.cast_zero, sub_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_right hbR.ne'
  have hratio (S : Act V 0) (T : Act E b2) : G.ratio S.1 T.1 = if T = emptyAct then 1 else 0 := by
    by_cases h : T = emptyAct
    · subst T
      simp [ratio, emptyAct]
    · have hv : T.1 ≠ ∅ := fun hv => h (Subtype.ext hv)
      simp [ratio, hv, F, CS, np20261028_act_zero_eq_empty S, h]
  unfold rate expPay
  simp_rw [hratio]
  simp [mul_ite, he]

 theorem np20261028_theorem_2_zero (G : DetectionModel V E) : np20261028_DetectionRateConclusion G 0 := by
  classical
  refine ⟨⟨0, le_rfl, zero_le_one, ?_⟩, ?_⟩
  · intro b2 hb hm σ1 σ2 hne
    exact np20261028_zero_budget_rate G hb (le_trans hm.le (np20261028_mStar_le_card G)) σ1 σ2 hne
  · intro σ1 σ2 hne b2 hb hm
    letI : Nonempty (Act E b2) := ⟨⟨∅, by simp⟩⟩
    letI : Nonempty (Act V 0) := ⟨⟨∅, by simp⟩⟩
    obtain ⟨τ2, τ1, hτ⟩ := np20261028_exists_isNashEq (G.payoff 0 b2)
    have heq : τ1 = σ1 := np20261028_mixed_zero_unique hτ.2.1 hne.2.1
    exact ⟨τ2, heq ▸ hτ⟩

lemma np20261028_undet_nonneg (G : DetectionModel V E) (S : Finset V) (T : Finset E) :
    0 ≤ G.undet S T := by
  unfold undet
  exact sub_nonneg.mpr (by exact_mod_cast (card_le_card (inter_subset_right : G.CS S ∩ T ⊆ T)))

lemma np20261028_U_nonneg (G : DetectionModel V E) {b1 b2 : ℕ}
    {σ1 : Act V b1 → ℝ} {σ2 : Act E b2 → ℝ}
    (h1 : IsMixed σ1) (h2 : IsMixed σ2) : 0 ≤ G.U σ1 σ2 := by
  exact sum_nonneg fun T _ => sum_nonneg fun S _ =>
    mul_nonneg (mul_nonneg (h2.1 T) (h1.1 S)) (np20261028_undet_nonneg G S.1 T.1)

lemma np20261028_ratio_eq_one_of_undet_eq_zero (G : DetectionModel V E) (S : Finset V) (T : Finset E)
    (h : G.undet S T = 0) : G.ratio S T = 1 := by
  unfold ratio
  split_ifs with ht
  · rfl
  · have hc : (T.card : ℝ) ≠ 0 := by exact_mod_cast (card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr ht))
    have hf : (G.F S T : ℝ) = T.card := by unfold undet at h; linarith
    rw [hf, div_self hc]

 theorem np20261028_rate_eq_one_of_U_eq_zero (G : DetectionModel V E) {b1 b2 : ℕ}
    {σ1 : Act V b1 → ℝ} {σ2 : Act E b2 → ℝ}
    (h1 : IsMixed σ1) (h2 : IsMixed σ2) (hu : G.U σ1 σ2 = 0) : G.rate σ1 σ2 = 1 := by
  classical
  have hn (T : Act E b2) (S : Act V b1) :
      0 ≤ σ2 T * σ1 S * G.undet S.1 T.1 :=
    mul_nonneg (mul_nonneg (h2.1 T) (h1.1 S)) (np20261028_undet_nonneg G S.1 T.1)
  have hz (T : Act E b2) (S : Act V b1) : σ2 T * σ1 S * G.undet S.1 T.1 = 0 := by
    have hrow := (sum_eq_zero_iff_of_nonneg fun T _ => sum_nonneg fun S _ => hn T S).mp hu T (mem_univ _)
    exact (sum_eq_zero_iff_of_nonneg fun S _ => hn T S).mp hrow S (mem_univ _)
  have ht (T : Act E b2) (S : Act V b1) : σ2 T * σ1 S * G.ratio S.1 T.1 = σ2 T * σ1 S := by
    by_cases hw : σ2 T * σ1 S = 0
    · rw [hw, zero_mul]
    · have hu' : G.undet S.1 T.1 = 0 := (mul_eq_zero.mp (hz T S)).resolve_left hw
      rw [np20261028_ratio_eq_one_of_undet_eq_zero G S.1 T.1 hu', mul_one]
  unfold rate expPay
  simp_rw [ht, ← mul_sum, h1.2, mul_one, h2.2]

lemma np20261028_exists_cover_le (G : DetectionModel V E) {b1 : ℕ} (hb : G.nStar ≤ b1) :
    ∃ S : Act V b1, G.IsSetCover S.1 := by
  have huniv : G.IsSetCover univ := by
    intro e
    obtain ⟨i, hi⟩ := G.coverable e
    have he : e ∈ G.CS univ := mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
    simp [F, he]
  have hne : {k | ∃ S : Finset V, S.card = k ∧ G.IsSetCover S}.Nonempty :=
    ⟨_, univ, rfl, huniv⟩
  obtain ⟨S, hS, hc⟩ := Nat.sInf_mem hne
  exact ⟨⟨S, hS ▸ hb⟩, hc⟩

lemma np20261028_cover_undet (G : DetectionModel V E) (S : Finset V) (hc : G.IsSetCover S)
    (T : Finset E) : G.undet S T = 0 := by
  have hmem e : e ∈ G.CS S := by
    have h := hc e
    by_contra hn
    simp [F, hn] at h
  have hsub : T ⊆ G.CS S := fun e _ => hmem e
  simp [undet, F, inter_eq_right.mpr hsub]

 theorem np20261028_equilibrium_U_zero_of_cover (G : DetectionModel V E) {b1 b2 : ℕ}
    (hb : G.nStar ≤ b1) {σ1 : Act V b1 → ℝ} {σ2 : Act E b2 → ℝ}
    (hne : G.IsNE b1 b2 σ1 σ2) : G.U σ1 σ2 = 0 := by
  classical
  obtain ⟨S, hc⟩ := np20261028_exists_cover_le G hb
  have hp : IsMixed (pureMixed S) := by
    constructor
    · intro a; simp only [pureMixed]; split_ifs <;> norm_num
    · simp [pureMixed]
  have h := hne.2.2.2 (pureMixed S) hp
  have hz : expPay (G.payoff b1 b2) σ2 (pureMixed S) = 0 := by
    simp [expPay, pureMixed, payoff, np20261028_cover_undet G S.1 hc]
  rw [hz] at h
  exact le_antisymm h (np20261028_U_nonneg G hne.2.1 hne.1)

lemma np20261028_U_pure_singleton (G : DetectionModel V E) {b1 : ℕ}
    (σ1 : Act V b1 → ℝ) (e : E) :
    G.U σ1 (pureMixed (⟨{e}, by simp⟩ : Act E 1)) = G.np20261028_missProb σ1 e := by
  classical
  simp [U, expPay, pureMixed, payoff, np20261028_undet_eq_sum, DetectionModel.np20261028_missProb]

 theorem np20261028_theorem_2_cover (G : DetectionModel V E) {b1 : ℕ} (hb : G.nStar ≤ b1) :
    np20261028_DetectionRateConclusion G b1 := by
  classical
  refine ⟨⟨1, zero_le_one, le_rfl, ?_⟩, ?_⟩
  · intro b2 hb2 hm σ1 σ2 hne
    exact np20261028_rate_eq_one_of_U_eq_zero G hne.2.1 hne.1 (np20261028_equilibrium_U_zero_of_cover G hb hne)
  · intro σ1 σ2 hne b2 hb2 hm
    have hu : G.U σ1 σ2 = 0 := np20261028_equilibrium_U_zero_of_cover G hb hne
    have hmiss (e : E) : G.np20261028_missProb σ1 e = 0 := by
      let t : Act E 1 := ⟨{e}, by simp⟩
      have ht : IsMixed (pureMixed t) := by
        constructor
        · intro a; simp only [pureMixed]; split_ifs <;> norm_num
        · simp [pureMixed]
      have h := hne.2.2.1 (pureMixed t) ht
      change G.U σ1 (pureMixed t) ≤ G.U σ1 σ2 at h
      rw [hu] at h
      have hh : G.U σ1 (pureMixed t) = G.np20261028_missProb σ1 e := np20261028_U_pure_singleton G σ1 e
      rw [hh] at h
      exact le_antisymm h (np20261028_missProb_nonneg G σ1 hne.2.1 e)
    have hzero (τ : Act E b2 → ℝ) : G.U σ1 τ = 0 := by
      rw [np20261028_U_eq_sum_marg]
      simp [hmiss]
    let emptyAct : Act E b2 := ⟨∅, by simp⟩
    have he : IsMixed (pureMixed emptyAct) := by
      constructor
      · intro a; simp only [pureMixed]; split_ifs <;> norm_num
      · simp [pureMixed]
    refine ⟨pureMixed emptyAct, he, hne.2.1, ?_, ?_⟩
    · intro τ hτ
      change G.U σ1 τ ≤ G.U σ1 (pureMixed emptyAct)
      rw [hzero, hzero]
    · intro τ hτ
      change G.U σ1 (pureMixed emptyAct) ≤ G.U τ (pureMixed emptyAct)
      rw [hzero]
      exact np20261028_U_nonneg G hτ he

end NetInspect.Rate








namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem np20261028_marg_nonneg_of_mixed {b : ℕ} (σ : Act E b → ℝ) (hσ : IsMixed σ) (e : E) :
    0 ≤ marg σ e := by
  classical
  unfold marg
  apply sum_nonneg
  intro T _
  split_ifs
  · exact hσ.1 T
  · exact le_rfl

theorem np20261028_complete_single_marginals [Nonempty E] (σ : Act E 1 → ℝ) (hσ : IsMixed σ) :
    ∃ q : E → ℝ, IsMixed q ∧ ∀ e, marg σ e ≤ q e := by
  classical
  let e0 : E := Classical.choice inferInstance
  let M := ∑ e, marg σ e
  have hM : M ≤ 1 := by simpa [M] using np20261028_sum_marg_le_budget σ hσ
  let q : E → ℝ := fun e => marg σ e + if e = e0 then 1 - M else 0
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · intro e
    exact add_nonneg (np20261028_marg_nonneg_of_mixed σ hσ e) (by split_ifs <;> linarith)
  · dsimp [q]
    rw [sum_add_distrib]
    simp [M]
    <;> ring
  · intro e
    dsimp [q]
    have : 0 ≤ if e = e0 then 1 - M else 0 := by split_ifs <;> linarith
    linarith

theorem np20261028_U_pure_eq_marg_sum {b1 b2 : ℕ} (G : DetectionModel V E)
    (S : Act V b1) (σ2 : Act E b2 → ℝ) :
    G.U (pureMixed S) σ2 = ∑ e, marg σ2 e * (if e ∈ G.CS S.1 then (0 : ℝ) else 1) := by
  classical
  rw [np20261028_U_eq_sum_marg]
  simp only [DetectionModel.np20261028_missProb, pureMixed, ite_mul, one_mul, zero_mul,
    sum_ite_eq', sum_ite_eq, mem_univ, ↓reduceIte]

theorem np20261028_sum_miss_eq_one_sub_coverage (G : DetectionModel V E)
    (q : E → ℝ) (hq : IsMixed q) (S : Finset V) :
    (∑ e, q e * (if e ∈ G.CS S then (0 : ℝ) else 1)) = 1 - ∑ e ∈ G.CS S, q e := by
  classical
  have he (e : E) : q e * (if e ∈ G.CS S then (0 : ℝ) else 1) =
      q e - if e ∈ G.CS S then q e else 0 := by split_ifs <;> simp
  simp_rw [he]
  rw [sum_sub_distrib, hq.2]
  simp

theorem np20261028_single_equilibrium_of_capped_coverage [Nonempty E] (G : DetectionModel V E)
    (b : ℕ) (hm : 1 < G.mStar) (p : E → ℝ) (hp : IsMixed p)
    (hcap : ∀ e, p e ≤ 1 / (G.mStar : ℝ)) (v : ℝ)
    (hupper : ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p e ≤ v)
    (hopt : ∀ q : E → ℝ, IsMixed q →
      ∃ S : Finset V, S.card ≤ b ∧ v ≤ ∑ e ∈ G.CS S, q e)
    (σ1 : Act V b → ℝ) (σ2 : Act E 1 → ℝ) (hne : G.IsNE b 1 σ1 σ2) :
    ∃ τ2 : Act E 1 → ℝ, G.IsNE b 1 σ1 τ2 ∧ (∀ e, marg τ2 e = p e) ∧
      G.U σ1 τ2 = 1 - v := by
  classical
  have hmR : (1 : ℝ) < G.mStar := by exact_mod_cast hm
  have hp1 : ∀ e, 0 ≤ p e ∧ p e ≤ 1 := by
    intro e
    exact ⟨hp.1 e, (hcap e).trans (by apply (div_le_one (by positivity)).2; linarith)⟩
  obtain ⟨τ2, hτ2, hmarg⟩ := np20261028_lemma_EC_4 G hm p hp1 (by simpa using hp.2)
  obtain ⟨q, hq, hqge⟩ := np20261028_complete_single_marginals σ2 hne.1
  obtain ⟨S, hS, hvS⟩ := hopt q hq
  let s : Act V b := ⟨S, hS⟩
  have hs : IsMixed (pureMixed s) := by
    constructor
    · intro X; simp only [pureMixed]; split_ifs <;> norm_num
    · simp [pureMixed]
  have huv : G.U σ1 σ2 ≤ 1 - v := by
    calc
      _ ≤ G.U (pureMixed s) σ2 := hne.2.2.2 (pureMixed s) hs
      _ ≤ ∑ e, q e * (if e ∈ G.CS S then (0 : ℝ) else 1) := by
        rw [np20261028_U_pure_eq_marg_sum]
        exact sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hqge e) (by split_ifs <;> norm_num)
      _ = 1 - ∑ e ∈ G.CS S, q e := np20261028_sum_miss_eq_one_sub_coverage G q hq S
      _ ≤ 1 - v := by linarith
  have hsecure (ρ : Act V b → ℝ) (hρ : IsMixed ρ) : 1 - v ≤ G.U ρ τ2 := by
    apply np20261028_le_expPay_of_pure_right (G.payoff b 1) τ2 hρ (1 - v)
    intro X
    change 1 - v ≤ G.U (pureMixed X) τ2
    rw [np20261028_U_pure_eq_marg_sum]
    simp_rw [hmarg]
    rw [np20261028_sum_miss_eq_one_sub_coverage G p hp]
    linarith [hupper X.1 X.2]
  have ht : G.U σ1 τ2 = 1 - v := le_antisymm
    ((hne.2.2.1 τ2 hτ2).trans huv) (hsecure σ1 hne.2.1)
  have horig : G.U σ1 σ2 = 1 - v := le_antisymm huv
    ((hsecure σ1 hne.2.1).trans (hne.2.2.1 τ2 hτ2))
  refine ⟨τ2, ⟨hτ2, hne.2.1, ?_, ?_⟩, hmarg, ht⟩
  · intro ρ hρ
    change G.U σ1 ρ ≤ G.U σ1 τ2
    rw [ht, ← horig]
    exact hne.2.2.1 ρ hρ
  · intro ρ hρ
    change G.U σ1 τ2 ≤ G.U ρ τ2
    rw [ht]
    exact hsecure ρ hρ

theorem np20261028_scale_capped_equilibrium (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (τ1 : Act E 1 → ℝ) (hne : G.IsNE b1 1 σ1 τ1)
    (p : E → ℝ) (hp : IsMixed p) (hmarg : ∀ e, marg τ1 e = p e)
    (hcap : ∀ e, p e ≤ 1 / (G.mStar : ℝ)) (hb2 : 1 ≤ b2) (hbm : b2 < G.mStar) :
    ∃ τ2 : Act E b2 → ℝ, G.IsNE b1 b2 σ1 τ2 ∧
      G.U σ1 τ2 = (b2 : ℝ) * G.U σ1 τ1 ∧
      ∀ e, G.np20261028_missProb σ1 e ≤ G.U σ1 τ1 := by
  classical
  have hmN : 0 < G.mStar := by omega
  have hmR : (0 : ℝ) < G.mStar := by exact_mod_cast hmN
  have hbR : (b2 : ℝ) < G.mStar := by exact_mod_cast hbm
  let ρ : E → ℝ := fun e => (b2 : ℝ) * p e
  have hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1 := by
    intro e
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (hp.1 e), ?_⟩
    calc
      ρ e ≤ (b2 : ℝ) * (1 / (G.mStar : ℝ)) :=
        mul_le_mul_of_nonneg_left (hcap e) (Nat.cast_nonneg _)
      _ = (b2 : ℝ) / G.mStar := by ring
      _ ≤ 1 := (div_le_one hmR).2 hbR.le
  have hsum : ∑ e, ρ e = (b2 : ℝ) := by simp [ρ, ← mul_sum, hp.2]
  obtain ⟨τ2, hτ2, hτmarg⟩ := np20261028_lemma_EC_4 G hbm ρ hρ hsum
  have hscale (σ : Act V b1 → ℝ) : G.U σ τ2 = (b2 : ℝ) * G.U σ τ1 := by
    apply np20261028_U_eq_mul_of_marg_eq_mul
    intro e
    rw [hτmarg, hmarg]
  have hmiss (e : E) : G.np20261028_missProb σ1 e ≤ G.U σ1 τ1 := by
    let t : Act E 1 := ⟨{e}, by simp⟩
    have ht : IsMixed (pureMixed t) := by
      constructor
      · intro X; simp only [pureMixed]; split_ifs <;> norm_num
      · simp [pureMixed]
    have hh := hne.2.2.1 (pureMixed t) ht
    change G.U σ1 (pureMixed t) ≤ G.U σ1 τ1 at hh
    simpa only [t, np20261028_U_pure_singleton] using hh
  have hu : 0 ≤ G.U σ1 τ1 := by
    rw [np20261028_U_eq_sum_marg]
    exact sum_nonneg fun e _ => mul_nonneg (np20261028_marg_nonneg_of_mixed τ1 hne.1 e)
      (np20261028_missProb_nonneg G σ1 hne.2.1 e)
  refine ⟨τ2, ⟨hτ2, hne.2.1, ?_, ?_⟩, hscale σ1, hmiss⟩
  · intro σ hσ
    change G.U σ1 σ ≤ G.U σ1 τ2
    rw [hscale σ1, np20261028_U_eq_sum_marg]
    calc
      _ ≤ ∑ e, marg σ e * G.U σ1 τ1 := sum_le_sum fun e _ =>
        mul_le_mul_of_nonneg_left (hmiss e) (np20261028_marg_nonneg_of_mixed σ hσ e)
      _ = (∑ e, marg σ e) * G.U σ1 τ1 := (sum_mul _ _ _).symm
      _ ≤ (b2 : ℝ) * G.U σ1 τ1 := mul_le_mul_of_nonneg_right (np20261028_sum_marg_le_budget σ hσ) hu
  · intro σ hσ
    change G.U σ1 τ2 ≤ G.U σ τ2
    rw [hscale σ1, hscale σ]
    exact mul_le_mul_of_nonneg_left (hne.2.2.2 σ hσ) (Nat.cast_nonneg _)

end NetInspect.Rate




namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem np20261028_gameValue_eq_U_of_NE (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (hne : G.IsNE b1 b2 σ1 σ2) :
    G.gameValue b1 b2 = G.U σ1 σ2 := by
  classical
  letI : Nonempty (Act E b2) := ⟨⟨∅, by simp⟩⟩
  change IsNashEq (G.payoff b1 b2) σ2 σ1 at hne
  have hpure (T : Act E b2) : IsMixed (pureMixed T) := by
    refine ⟨fun X => ?_, ?_⟩
    · unfold pureMixed; split_ifs <;> norm_num
    · simp [pureMixed]
  have hupper (τ1 : Act V b1 → ℝ) : G.U τ1 σ2 ≤ G.worst1 b2 τ1 := by
    apply np20261028_expPay_le_of_pure_left (G.payoff b1 b2) hne.1 τ1
    intro T
    exact le_csSup (Set.finite_range (fun X : Act E b2 => G.U τ1 (pureMixed X))).bddAbove
      (Set.mem_range_self T)
  have hvalue : G.worst1 b2 σ1 = G.U σ1 σ2 := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro x ⟨T, rfl⟩
      exact hne.2.2.1 _ (hpure T)
    · exact hupper σ1
  have hlower (τ1 : Act V b1 → ℝ) (hτ1 : IsMixed τ1) :
      G.U σ1 σ2 ≤ G.worst1 b2 τ1 :=
    (hne.2.2.2 τ1 hτ1).trans (hupper τ1)
  have hneSet : ((G.worst1 b2) '' {τ1 : Act V b1 → ℝ | IsMixed τ1}).Nonempty :=
    ⟨G.worst1 b2 σ1, σ1, hne.2.1, rfl⟩
  have hbounded : BddBelow ((G.worst1 b2) '' {τ1 : Act V b1 → ℝ | IsMixed τ1}) := by
    refine ⟨G.U σ1 σ2, ?_⟩
    rintro x ⟨τ1, hτ1, rfl⟩
    exact hlower τ1 hτ1
  apply le_antisymm
  · exact (csInf_le hbounded ⟨σ1, hne.2.1, rfl⟩).trans hvalue.le
  · apply le_csInf hneSet
    rintro x ⟨τ1, hτ1, rfl⟩
    exact hlower τ1 hτ1

end NetInspect.Rate



namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow Aux_NetInspect_Rate_lemma_EC_3
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem np20261028_cyc_marg_outside {m b : ℕ} (y : Fin m → E) (e : E) (he : e ∉ univ.image y) :
    marg (cycStrat y b) e = 0 := by
  classical
  have hw (k : Fin m) : e ∉ window y b k := by
    intro h
    obtain ⟨j, _, hj⟩ := mem_image.mp h
    exact he (mem_image.mpr ⟨_, mem_univ _, hj⟩)
  unfold marg cycStrat
  apply sum_eq_zero
  intro X _
  split_ifs with heX
  · have hz : (univ.filter (fun k : Fin m => window y b k = X.1)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro k hk
      have hk' := (mem_filter.mp hk).2
      exact hw k (hk'.symm ▸ heX)
    simp [hz]
  · rfl

theorem np20261028_cyclic_packing_pure_payoff (G : DetectionModel V E) {b1 b2 m : ℕ}
    (y : Fin m → E) (hy : Function.Injective y) (hm : 0 < m) (hb : b2 ≤ m)
    (S : Act V b1) :
    G.U (pureMixed S) (cycStrat y b2) =
      ((b2 : ℝ) / m) * ((m : ℝ) - G.F S.1 (univ.image y)) := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  have hmarg (e : E) : marg (cycStrat y b2) e =
      if e ∈ univ.image y then (b2 : ℝ) / m else 0 := by
    by_cases he : e ∈ univ.image y
    · obtain ⟨j, _, rfl⟩ := mem_image.mp he
      rw [if_pos (mem_image.mpr ⟨j, mem_univ _, rfl⟩)]
      exact np20261028_margv y hy hb j
    · rw [if_neg he]
      exact np20261028_cyc_marg_outside y e he
  rw [np20261028_U_pure_eq_marg_sum]
  simp_rw [hmarg, ite_mul, zero_mul]
  simp only [sum_ite_mem]
  rw [← mul_sum, ← np20261028_undet_eq_sum]
  unfold undet
  rw [univ_inter]
  rw [card_image_of_injective _ hy]
  simp

theorem np20261028_packing_attains_budget (G : DetectionModel V E) (T : Finset E) (b : ℕ) :
    ∃ S : Act V b, min b T.card ≤ G.F S.1 T := by
  classical
  obtain ⟨A, hAT, hA⟩ := exists_subset_card_eq (s := T) (Nat.min_le_right b T.card)
  choose f hf using G.coverable
  let S := A.image f
  have hS : S.card ≤ b := by
    exact (card_image_le.trans hA.le).trans (Nat.min_le_left _ _)
  refine ⟨⟨S, hS⟩, ?_⟩
  rw [← hA]
  apply card_le_card
  intro e he
  refine mem_inter.mpr ⟨?_, hAT he⟩
  exact mem_biUnion.mpr ⟨f e, mem_image.mpr ⟨e, he, rfl⟩, hf e⟩

theorem np20261028_prop1_packing (G : DetectionModel V E) {b1 b2 : ℕ} (hb2 : 1 ≤ b2)
    (m : ℕ) (y : Fin m → E) (hy : Function.Injective y)
    (hpack : G.IsSetPacking (univ.image y)) (hb2m : b2 ≤ m) :
    G.best2 b1 (cycStrat y b2) = max 0 ((b2 : ℝ) * (1 - (b1 : ℝ) / m)) ∧
      max 0 ((b2 : ℝ) * (1 - (b1 : ℝ) / m)) ≤ G.gameValue b1 b2 := by
  classical
  have hmN : 0 < m := by omega
  have hm : (0 : ℝ) < m := by exact_mod_cast hmN
  have hb : (0 : ℝ) ≤ b2 := Nat.cast_nonneg _
  have hc : 0 ≤ (b2 : ℝ) / m := div_nonneg hb hm.le
  let T := univ.image y
  have hTcard : T.card = m := by simp [T, card_image_of_injective _ hy]
  let L := max 0 ((b2 : ℝ) * (1 - (b1 : ℝ) / m))
  have hid : (b2 : ℝ) * (1 - (b1 : ℝ) / m) = ((b2 : ℝ) / m) * ((m : ℝ) - b1) := by
    field_simp
    <;> ring
  have hbound (S : Act V b1) : L ≤ G.U (pureMixed S) (cycStrat y b2) := by
    rw [np20261028_cyclic_packing_pure_payoff G y hy hmN hb2m S]
    have hfB : (G.F S.1 T : ℝ) ≤ b1 := by
      exact_mod_cast (np20261028_F_le_card_of_packing G S.1 T hpack).trans S.2
    have hfM : (G.F S.1 T : ℝ) ≤ m := by
      have hh : G.F S.1 T ≤ T.card := card_le_card inter_subset_right
      rw [hTcard] at hh
      exact_mod_cast hh
    apply max_le
    · exact mul_nonneg hc (by dsimp [T] at hfM; linarith)
    · rw [hid]
      apply mul_le_mul_of_nonneg_left _ hc
      dsimp [T] at hfB
      linarith
  obtain ⟨S, hS⟩ := np20261028_packing_attains_budget G T b1
  have hF : G.F S.1 T = min b1 m := by
    apply le_antisymm
    · apply le_min
      · exact (np20261028_F_le_card_of_packing G S.1 T hpack).trans S.2
      · have hh : G.F S.1 T ≤ T.card := card_le_card inter_subset_right
        simpa [hTcard] using hh
    · simpa [hTcard] using hS
  have hattain : G.U (pureMixed S) (cycStrat y b2) = L := by
    rw [np20261028_cyclic_packing_pure_payoff G y hy hmN hb2m S]
    change ((b2 : ℝ) / m) * ((m : ℝ) - (G.F S.1 T : ℝ)) = L
    rw [hF]
    dsimp [L]
    rw [hid]
    by_cases hbm : b1 ≤ m
    · have hsub : (0 : ℝ) ≤ (m : ℝ) - b1 := sub_nonneg.mpr (by exact_mod_cast hbm)
      rw [min_eq_left hbm, max_eq_right (mul_nonneg hc hsub)]
    · have hmb : m ≤ b1 := by omega
      have hsub : (m : ℝ) - b1 ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hmb)
      rw [min_eq_right hmb, sub_self, mul_zero, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc hsub)]
  letI : Nonempty (Act V b1) := ⟨⟨∅, by simp⟩⟩
  letI : Nonempty (Act E b2) := ⟨⟨∅, by simp⟩⟩
  have hbest : G.best2 b1 (cycStrat y b2) = L := by
    apply le_antisymm
    · calc
        _ ≤ G.U (pureMixed S) (cycStrat y b2) :=
          csInf_le (Set.finite_range (fun X : Act V b1 =>
            G.U (pureMixed X) (cycStrat y b2))).bddBelow (Set.mem_range_self S)
        _ = L := hattain
    · apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨X, rfl⟩
      exact hbound X
  refine ⟨hbest, ?_⟩
  obtain ⟨σ2, σ1, hne⟩ := np20261028_exists_isNashEq (G.payoff b1 b2)
  have hcyc : IsMixed (cycStrat y b2) := np20261028_mixed y hmN
  rw [np20261028_gameValue_eq_U_of_NE G σ1 σ2 hne]
  have hlow : L ≤ G.U σ1 (cycStrat y b2) :=
    np20261028_le_expPay_of_pure_right (G.payoff b1 b2) (cycStrat y b2) hne.2.1 L hbound
  exact hlow.trans (hne.2.2.1 _ hcyc)

end NetInspect.Rate




namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow Aux_NetInspect_Rate_lemma_EC_3
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem np20261028_private_component_of_minimal (G : DetectionModel V E) (S : Finset V)
    (hS : G.IsMinimalSetCover S) (i : V) (hi : i ∈ S) :
    ∃ e : E, e ∈ G.C i ∧ ∀ j ∈ S, e ∈ G.C j → j = i := by
  classical
  have hnot := hS.2 i hi
  change ¬ ∀ e : E, G.F (S.erase i) {e} = 1 at hnot
  push Not at hnot
  obtain ⟨e, he⟩ := hnot
  have hdel : e ∉ G.CS (S.erase i) := by
    intro h
    exact he (by simp [F, h])
  have hcov : e ∈ G.CS S := by
    by_contra h
    have hh := hS.1 e
    simp [F, h] at hh
  obtain ⟨j, hj, hje⟩ := mem_biUnion.mp hcov
  have hji : j = i := by
    by_contra h
    exact hdel (mem_biUnion.mpr ⟨j, mem_erase.mpr ⟨h, hj⟩, hje⟩)
  refine ⟨e, hji ▸ hje, ?_⟩
  intro k hk hke
  by_contra h
  exact hdel (mem_biUnion.mpr ⟨k, mem_erase.mpr ⟨h, hk⟩, hke⟩)

theorem np20261028_window_subset_image {α : Type*} [DecidableEq α] {n b : ℕ}
    (x : Fin n → α) (k : Fin n) : window x b k ⊆ univ.image x := by
  intro a ha
  obtain ⟨j, _, rfl⟩ := mem_image.mp ha
  exact mem_image.mpr ⟨_, mem_univ _, rfl⟩

theorem np20261028_cycStrat_zero_of_not_subset {α : Type*} [Fintype α] [DecidableEq α] {n b : ℕ}
    (x : Fin n → α) (X : Act α b) (hX : ¬ X.1 ⊆ univ.image x) : cycStrat x b X = 0 := by
  classical
  have hf : (univ.filter fun k : Fin n => window x b k = X.1) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro k _ hk
    exact hX (hk ▸ np20261028_window_subset_image x k)
  simp [cycStrat, hf]

theorem np20261028_missProb_add_marg_le_one (G : DetectionModel V E) {b : ℕ}
    (σ : Act V b → ℝ) (hσ : IsMixed σ) (i : V) (e : E) (he : e ∈ G.C i) :
    G.np20261028_missProb σ e + marg σ i ≤ 1 := by
  unfold DetectionModel.np20261028_missProb marg
  rw [← sum_add_distrib]
  calc
    _ ≤ ∑ X, σ X := by
      apply sum_le_sum
      intro X _
      by_cases hi : i ∈ X.1
      · have heX : e ∈ G.CS X.1 := mem_biUnion.mpr ⟨i, hi, he⟩
        simp [hi, heX]
      · simp only [hi, ↓reduceIte, add_zero]
        split_ifs <;> simp [hσ.1 X]
    _ = 1 := hσ.2

theorem np20261028_missProb_cyclic_private (G : DetectionModel V E) {n b : ℕ}
    (x : Fin n → V) (hn : 0 < n) (hx : Function.Injective x) (hb : b ≤ n)
    (j : Fin n) (e : E) (he : e ∈ G.C (x j))
    (hprivate : ∀ i ∈ univ.image x, e ∈ G.C i → i = x j) :
    G.np20261028_missProb (cycStrat x b) e = 1 - (b : ℝ) / n := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  have hm := np20261028_mixed (b := b) x hn
  have hsum : G.np20261028_missProb (cycStrat x b) e + marg (cycStrat x b) (x j) = 1 := by
    unfold DetectionModel.np20261028_missProb marg
    rw [← sum_add_distrib]
    calc
      _ = ∑ X, cycStrat x b X := by
        apply sum_congr rfl
        intro X _
        by_cases hzero : cycStrat x b X = 0
        · simp [hzero]
        · have hsub : X.1 ⊆ univ.image x := by
            by_contra h
            exact hzero (np20261028_cycStrat_zero_of_not_subset x X h)
          have hiff : e ∈ G.CS X.1 ↔ x j ∈ X.1 := by
            constructor
            · intro h
              obtain ⟨i, hi, hie⟩ := mem_biUnion.mp h
              exact hprivate i (hsub hi) hie ▸ hi
            · intro h
              exact mem_biUnion.mpr ⟨x j, h, he⟩
          by_cases hmem : x j ∈ X.1 <;> simp [hiff, hmem]
      _ = 1 := hm.2
  rw [np20261028_margv x hx hb j] at hsum
  linarith

theorem np20261028_U_pure_attack_sum_miss (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ : Act V b1 → ℝ) (T : Act E b2) :
    G.U σ (pureMixed T) = ∑ e ∈ T.1, G.np20261028_missProb σ e := by
  rw [np20261028_U_eq_sum_marg]
  have hm (e : E) : marg (pureMixed T) e = if e ∈ T.1 then 1 else 0 := by
    unfold marg pureMixed
    rw [sum_eq_single T]
    · simp
    · intro X _ hXT; simp [hXT]
    · intro h; exact False.elim (h (mem_univ T))
  simp only [hm, ite_mul, one_mul, zero_mul]
  simp

end NetInspect.Rate

namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow Aux_NetInspect_Rate_lemma_EC_3
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The packing-to-cover injection used in the accepted proof of Lemma EC.2. -/
theorem np20261028_packing_card_le_cover (G : DetectionModel V E) (S : Finset V)
    (hS : G.IsSetCover S) (T : Finset E) (hT : G.IsSetPacking T) : T.card ≤ S.card := by
  classical
  have hcov (e : E) : ∃ i ∈ S, e ∈ G.C i := by
    have hh := hS e
    have he : e ∈ G.CS S := by
      by_contra h; simp [F, h] at hh
    exact mem_biUnion.mp he
  choose f hfS hfC using hcov
  refine card_le_card_of_injOn f (fun e _ => hfS e) ?_
  intro e1 he1 e2 he2 heq
  have hp := hT (f e1)
  have h1 : e1 ∈ G.C (f e1) ∩ T := mem_inter.mpr ⟨hfC e1, he1⟩
  have h2 : e2 ∈ G.C (f e1) ∩ T := mem_inter.mpr ⟨heq ▸ hfC e2, he2⟩
  simp only [F, CS, singleton_biUnion] at hp
  exact card_le_one.mp hp e1 h1 e2 h2

/-- The minimal-cover cyclic strategy has the exact worst-response value from Proposition 1. -/
theorem np20261028_prop1_minimal_cover (G : DetectionModel V E) {b1 b2 : ℕ}
    (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar)
    (n : ℕ) (x : Fin n → V) (hx : Function.Injective x)
    (hminimal : G.IsMinimalSetCover (univ.image x)) :
    G.worst1 b2 (cycStrat x b1) = (b2 : ℝ) * (1 - (b1 : ℝ) / n) ∧
      G.gameValue b1 b2 ≤ (b2 : ℝ) * (1 - (b1 : ℝ) / n) := by
  classical
  letI : Nonempty (Act E b2) := ⟨⟨∅, by simp⟩⟩
  have hxcard : (univ.image x).card = n := by rw [card_image_of_injective _ hx]; simp
  have hns : G.nStar ≤ n := Nat.sInf_le ⟨univ.image x, hxcard, hminimal.1⟩
  obtain ⟨Tmax, hmax, hpack⟩ := np20261028_exists_max_packing G
  have hmn : G.mStar ≤ n := by
    rw [← hmax, ← hxcard]
    exact np20261028_packing_card_le_cover G _ hminimal.1 _ hpack
  have hb2n : b2 ≤ n := hb2m.le.trans hmn
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hb2.trans hb2n)
  have hb1n : b1 ≤ n := hb1.le.trans hns
  letI : NeZero n := ⟨hn.ne'⟩
  have hσ : IsMixed (cycStrat x b1) := np20261028_mixed x hn
  let t : ℝ := 1 - (b1 : ℝ) / n
  have ht : 0 ≤ t := by
    dsimp [t]
    apply sub_nonneg.mpr
    exact (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr (by exact_mod_cast hb1n)
  have hmiss (e : E) : G.np20261028_missProb (cycStrat x b1) e ≤ t := by
    have hh := hminimal.1 e
    have he : e ∈ G.CS (univ.image x) := by
      by_contra h; simp [F, h] at hh
    obtain ⟨i, hi, hie⟩ := mem_biUnion.mp he
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    have hu := np20261028_missProb_add_marg_le_one G (cycStrat x b1) hσ (x j) e hie
    rw [np20261028_margv x hx hb1n j] at hu
    dsimp [t]; linarith
  have hupper (T : Act E b2) : G.U (cycStrat x b1) (pureMixed T) ≤ (b2 : ℝ) * t := by
    rw [np20261028_U_pure_attack_sum_miss]
    calc
      _ ≤ ∑ _e ∈ T.1, t := sum_le_sum fun e _ => hmiss e
      _ = (T.1.card : ℝ) * t := by simp [nsmul_eq_mul]
      _ ≤ (b2 : ℝ) * t := mul_le_mul_of_nonneg_right (by exact_mod_cast T.2) ht
  have hpriv (j : Fin n) : ∃ e : E, e ∈ G.C (x j) ∧
      ∀ i ∈ univ.image x, e ∈ G.C i → i = x j :=
    np20261028_private_component_of_minimal G _ hminimal (x j) (mem_image.mpr ⟨j, mem_univ _, rfl⟩)
  choose f hfC hfPrivate using hpriv
  have hf : Function.Injective f := by
    intro j k h
    apply hx
    exact (hfPrivate j (x k) (mem_image.mpr ⟨k, mem_univ _, rfl⟩)
      (by simpa [h] using hfC k)).symm
  let q : Fin b2 → E := fun j => f (Fin.castLE hb2n j)
  have hq : Function.Injective q := hf.comp (Fin.castLE_injective hb2n)
  let T : Finset E := univ.image q
  have hTc : T.card = b2 := by dsimp [T]; rw [card_image_of_injective _ hq]; simp
  let A : Act E b2 := ⟨T, hTc.le⟩
  have hTexact : G.U (cycStrat x b1) (pureMixed A) = (b2 : ℝ) * t := by
    rw [np20261028_U_pure_attack_sum_miss]
    calc
      _ = ∑ _e ∈ T, t := by
        apply sum_congr rfl
        intro e he
        obtain ⟨j, _, rfl⟩ := mem_image.mp he
        exact np20261028_missProb_cyclic_private G x hn hx hb1n (Fin.castLE hb2n j) _
          (hfC _) (hfPrivate _)
      _ = (b2 : ℝ) * t := by simp [hTc, nsmul_eq_mul]
  have hworst : G.worst1 b2 (cycStrat x b1) = (b2 : ℝ) * t := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro z ⟨B, rfl⟩
      exact hupper B
    · rw [← hTexact]
      exact le_csSup (Set.finite_range (fun B : Act E b2 =>
        G.U (cycStrat x b1) (pureMixed B))).bddAbove (Set.mem_range_self A)
  refine ⟨hworst, ?_⟩
  letI : Nonempty (Act E b2) := ⟨⟨∅, by simp⟩⟩
  letI : Nonempty (Act V b1) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨σ2, σ1, hne⟩ := np20261028_exists_isNashEq (G.payoff b1 b2)
  rw [np20261028_gameValue_eq_U_of_NE G σ1 σ2 hne]
  exact (hne.2.2.2 (cycStrat x b1) hσ).trans
    (np20261028_expPay_le_of_pure_left (G.payoff b1 b2) hne.1 (cycStrat x b1) _ hupper)

end NetInspect.Rate


namespace NetInspect.Rate

open Finset DetectionModel

/-- Proposition 1 (p. 13), under the standing assumptions `b1 < n*`, `b2 < m*` of §3.3 and
`1 ≤ b2`: for every minimal set cover `S' = {x 0, …, x (n-1)}`,
`U*(b1, b2) ≤ max_{T∈A2} U(σ1(S', b1), T) = b2 (1 − b1/|S'|)`, and for every set packing
`T' = {y 0, …, y (m-1)}` with `m ≥ b2`,
`max{0, b2 (1 − b1/|T'|)} = min_{S∈A1} U(S, σ2(T', b2)) ≤ U*(b1, b2)`. -/
theorem np20261028_proposition_1 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b1 b2 : ℕ} (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar) :
    (∀ (n : ℕ) (x : Fin n → V), Function.Injective x → G.IsMinimalSetCover (univ.image x) →
      G.worst1 b2 (cycStrat x b1) = (b2 : ℝ) * (1 - (b1 : ℝ) / (n : ℝ)) ∧
      G.gameValue b1 b2 ≤ (b2 : ℝ) * (1 - (b1 : ℝ) / (n : ℝ))) ∧
    (∀ (m : ℕ) (y : Fin m → E), Function.Injective y → G.IsSetPacking (univ.image y) → b2 ≤ m →
      G.best2 b1 (cycStrat y b2) = max 0 ((b2 : ℝ) * (1 - (b1 : ℝ) / (m : ℝ))) ∧
      max 0 ((b2 : ℝ) * (1 - (b1 : ℝ) / (m : ℝ))) ≤ G.gameValue b1 b2)  := by
  constructor
  · intro n x hx hminimal
    exact np20261028_prop1_minimal_cover G hb1 hb2 hb2m n x hx hminimal
  · intro m y hy hpacking hb
    exact np20261028_prop1_packing G hb2 m y hy hpacking hb

end NetInspect.Rate


open NetInspect.Rate NetInspect.Rate.DetectionModel Finset

theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b1 b2 : ℕ} (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar) :
    (∀ (n : ℕ) (x : Fin n → V), Function.Injective x → G.IsMinimalSetCover (univ.image x) →
      G.worst1 b2 (cycStrat x b1) = (b2 : ℝ) * (1 - (b1 : ℝ) / (n : ℝ)) ∧
      G.gameValue b1 b2 ≤ (b2 : ℝ) * (1 - (b1 : ℝ) / (n : ℝ))) ∧
    (∀ (m : ℕ) (y : Fin m → E), Function.Injective y → G.IsSetPacking (univ.image y) → b2 ≤ m →
      G.best2 b1 (cycStrat y b2) = max 0 ((b2 : ℝ) * (1 - (b1 : ℝ) / (m : ℝ))) ∧
      max 0 ((b2 : ℝ) * (1 - (b1 : ℝ) / (m : ℝ))) ≤ G.gameValue b1 b2) := by
  exact NetInspect.Rate.np20261028_proposition_1 G hb1 hb2 hb2m

#print axioms solution
