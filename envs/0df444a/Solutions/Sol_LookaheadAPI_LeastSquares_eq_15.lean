-- Prove2me | solution 1 for LookaheadAPI.LeastSquares.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:53:01.199126+00:00
-- url     : https://prove2.me/submissions/d3c9208d-80bc-40a1-89b9-b66f3d40939b

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace Aux_LA_TH1
open FoundationsML.ReinforcementLearning LookaheadAPI.LeastSquares Matrix

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

lemma it_det (M : MDP S A) (μ : S → A) (s s' : S) :
    InducedTransition (detPolicy μ) M.P s s' = M.P s (μ s) s' := by
  unfold InducedTransition detPolicy
  simp [ite_mul]

lemma ir_det (M : MDP S A) (μ : S → A) (s : S) :
    InducedReward (detPolicy μ) M.r s = M.r s (μ s) := by
  unfold InducedReward detPolicy
  simp [ite_mul]

lemma occ_fwd (M : MDP S A) (μ : S → A) (s0 : S) (t : ℕ) (s' : S) :
    OccupationDist (detPolicy μ) M.P s0 (t + 1) s' =
      ∑ s, OccupationDist (detPolicy μ) M.P s0 t s * M.P s (μ s) s' := by
  simp only [OccupationDist, it_det]

lemma occ_basic (M : MDP S A) (μ : S → A) (s0 : S) (t : ℕ) :
    (∀ s', 0 ≤ OccupationDist (detPolicy μ) M.P s0 t s') ∧
      ∑ s', OccupationDist (detPolicy μ) M.P s0 t s' = 1 := by
  have hk : ∀ s a, ∑ s', M.P s a s' = 1 := fun s a => (M.kernel s a).2
  induction t with
  | zero =>
    refine ⟨fun s' => ?_, ?_⟩
    · simp only [OccupationDist]
      split_ifs <;> norm_num
    · simp [OccupationDist]
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · rw [occ_fwd]
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) ((M.kernel s (μ s)).1 s'))
    · simp only [occ_fwd]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hk, mul_one]
      exact ih.2

lemma occ_bwd (M : MDP S A) (μ : S → A) (t : ℕ) : ∀ s0 s',
    OccupationDist (detPolicy μ) M.P s0 (t + 1) s' =
      ∑ j, M.P s0 (μ s0) j * OccupationDist (detPolicy μ) M.P j t s' := by
  induction t with
  | zero =>
    intro s0 s'
    rw [occ_fwd]
    simp [OccupationDist]
  | succ t ih =>
    intro s0 s'
    rw [occ_fwd]
    simp only [ih s0]
    simp only [occ_fwd]
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

noncomputable def fR (M : MDP S A) (μ : S → A) (t : ℕ) (s : S) : ℝ :=
  ∑ s', OccupationDist (detPolicy μ) M.P s t s' * M.r s' (μ s')

lemma fR_bd (M : MDP S A) (μ : S → A) (t : ℕ) (s : S) :
    0 ≤ fR M μ t s ∧ fR M μ t s ≤ 1 := by
  obtain ⟨h0, h1⟩ := occ_basic M μ s t
  unfold fR
  constructor
  · exact Finset.sum_nonneg (fun s' _ => mul_nonneg (h0 s') (M.r_mem s' (μ s')).1)
  · calc ∑ s', OccupationDist (detPolicy μ) M.P s t s' * M.r s' (μ s')
          ≤ ∑ s', OccupationDist (detPolicy μ) M.P s t s' :=
          Finset.sum_le_sum (fun s' _ => mul_le_of_le_one_right (h0 s') (M.r_mem s' (μ s')).2)
      _ = 1 := h1

lemma fR_succ (M : MDP S A) (μ : S → A) (t : ℕ) (s : S) :
    fR M μ (t + 1) s = ∑ j, M.P s (μ s) j * fR M μ t j := by
  unfold fR
  simp only [occ_bwd, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma fR_zero (M : MDP S A) (μ : S → A) (s : S) : fR M μ 0 s = M.r s (μ s) := by
  unfold fR
  simp [OccupationDist]

lemma valueOf_eq (M : MDP S A) (μ : S → A) (s : S) :
    valueOf M μ s = ∑' t, M.α ^ t * fR M μ t s := by
  unfold valueOf PolicyValue fR
  simp only [ir_det]

lemma hsum (M : MDP S A) (μ : S → A) (s : S) : Summable (fun t => M.α ^ t * fR M μ t s) :=
  Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg M.α_pos.le t) (fR_bd M μ t s).1)
    (fun t => mul_le_of_le_one_right (pow_nonneg M.α_pos.le t) (fR_bd M μ t s).2)
    (summable_geometric_of_lt_one M.α_pos.le M.α_lt_one)

lemma valueOf_fix (M : MDP S A) (μ : S → A) (s : S) :
    valueOf M μ s = policyOp M μ (valueOf M μ) s := by
  unfold policyOp
  simp only [valueOf_eq]
  have key : ∀ t, M.α ^ (t + 1) * fR M μ (t + 1) s =
      M.α * ∑ j, M.P s (μ s) j * (M.α ^ t * fR M μ t j) := by
    intro t
    simp only [fR_succ, pow_succ, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have htail : ∑' t, M.α ^ (t + 1) * fR M μ (t + 1) s =
      M.α * ∑ j, M.P s (μ s) j * ∑' t, M.α ^ t * fR M μ t j := by
    calc ∑' t, M.α ^ (t + 1) * fR M μ (t + 1) s
        = ∑' t, M.α * ∑ j, M.P s (μ s) j * (M.α ^ t * fR M μ t j) := tsum_congr key
      _ = M.α * ∑' t, ∑ j, M.P s (μ s) j * (M.α ^ t * fR M μ t j) := tsum_mul_left
      _ = M.α * ∑ j, ∑' t, M.P s (μ s) j * (M.α ^ t * fR M μ t j) := by
          congr 1
          exact Summable.tsum_finsetSum (fun j _ => (hsum M μ j).mul_left _)
      _ = M.α * ∑ j, M.P s (μ s) j * ∑' t, M.α ^ t * fR M μ t j := by
          congr 1
          exact Finset.sum_congr rfl (fun j _ => tsum_mul_left)
  rw [(hsum M μ s).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, fR_zero, htail]

lemma bell_eq [Nonempty A] (M : MDP S A) (J : S → ℝ) (s : S) :
    bellmanOp M J s = Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.r s a + M.α * ∑ s', M.P s a s' * J s') := rfl

lemma opt_ge [Nonempty A] (M : MDP S A) (μ : S → A) (s : S) :
    valueOf M μ s ≤ optValue M s := by
  unfold optValue
  exact Finset.le_sup' (fun μ => valueOf M μ s) (Finset.mem_univ μ)

lemma T_ge [Nonempty A] (M : MDP S A) (s : S) :
    optValue M s ≤ bellmanOp M (optValue M) s := by
  have hopt : optValue M s =
      Finset.univ.sup' Finset.univ_nonempty (fun μ : S → A => valueOf M μ s) := rfl
  rw [hopt]
  refine Finset.sup'_le _ _ (fun μ _ => ?_)
  calc valueOf M μ s = policyOp M μ (valueOf M μ) s := valueOf_fix M μ s
    _ ≤ policyOp M μ (optValue M) s := by
        unfold policyOp
        have h1 : ∑ j, M.P s (μ s) j * valueOf M μ j ≤ ∑ j, M.P s (μ s) j * optValue M j :=
          Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_left (opt_ge M μ j) ((M.kernel s (μ s)).1 j))
        have h2 := mul_le_mul_of_nonneg_left h1 M.α_pos.le
        linarith
    _ ≤ bellmanOp M (optValue M) s := by
        rw [bell_eq]
        exact Finset.le_sup' (fun a => M.r s a + M.α * ∑ s', M.P s a s' * optValue M s')
          (Finset.mem_univ (μ s))

lemma opt_fix [Nonempty S] [Nonempty A] (M : MDP S A) :
    bellmanOp M (optValue M) = optValue M := by
  have hg : ∀ s, ∃ a, bellmanOp M (optValue M) s =
      M.r s a + M.α * ∑ s', M.P s a s' * optValue M s' := fun s => by
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun a => M.r s a + M.α * ∑ s', M.P s a s' * optValue M s')
    exact ⟨a, by rw [bell_eq]; exact ha⟩
  choose μ' hμ' using hg
  have hD : ∀ s, optValue M s - valueOf M μ' s ≤
      M.α * ∑ j, M.P s (μ' s) j * (optValue M j - valueOf M μ' j) := by
    intro s
    have h1 := T_ge M s
    rw [hμ' s] at h1
    have h2 := valueOf_fix M μ' s
    unfold policyOp at h2
    have h3 : ∑ j, M.P s (μ' s) j * (optValue M j - valueOf M μ' j) =
        ∑ j, M.P s (μ' s) j * optValue M j - ∑ j, M.P s (μ' s) j * valueOf M μ' j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => mul_sub _ _ _)
    rw [h3, mul_sub]
    linarith
  obtain ⟨Dm, hDm⟩ : ∃ Dm, Dm = Finset.univ.sup' Finset.univ_nonempty
      (fun s => optValue M s - valueOf M μ' s) := ⟨_, rfl⟩
  have hle : ∀ s, optValue M s - valueOf M μ' s ≤ Dm := fun s => by
    rw [hDm]
    exact Finset.le_sup' (fun s => optValue M s - valueOf M μ' s) (Finset.mem_univ s)
  have hk : ∀ s a, ∑ s', M.P s a s' = 1 := fun s a => (M.kernel s a).2
  have hstep : ∀ s, optValue M s - valueOf M μ' s ≤ M.α * Dm := by
    intro s
    have h1 : ∑ j, M.P s (μ' s) j * (optValue M j - valueOf M μ' j) ≤ Dm := by
      calc ∑ j, M.P s (μ' s) j * (optValue M j - valueOf M μ' j)
          ≤ ∑ j, M.P s (μ' s) j * Dm :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (hle j) ((M.kernel s (μ' s)).1 j))
        _ = Dm := by rw [← Finset.sum_mul, hk, one_mul]
    have h2 := mul_le_mul_of_nonneg_left h1 M.α_pos.le
    linarith [hD s]
  have hDm_le : Dm ≤ M.α * Dm := by
    rw [hDm]
    refine Finset.sup'_le _ _ (fun s _ => ?_)
    rw [← hDm]
    exact hstep s
  have hDm0 : Dm ≤ 0 := by nlinarith [M.α_lt_one]
  have heq : optValue M = valueOf M μ' := by
    funext s
    have := hle s
    have := opt_ge M μ' s
    linarith
  funext s
  rw [hμ' s]
  have h2 := valueOf_fix M μ' s
  unfold policyOp at h2
  rw [heq]
  linarith

lemma sup'_le_add {ι : Type*} (s : Finset ι) (H : s.Nonempty) (f g : ι → ℝ) (c : ℝ)
    (h : ∀ i ∈ s, f i ≤ g i + c) : s.sup' H f ≤ s.sup' H g + c := by
  refine Finset.sup'_le H f (fun i hi => ?_)
  have hle : g i ≤ s.sup' H g := Finset.le_sup' g hi
  linarith [h i hi]

/-! ## Sup-norm helpers -/

lemma abs_le_norm' (f : S → ℝ) (s : S) : |f s| ≤ ‖f‖ := by
  have := norm_le_pi_norm f s
  rwa [Real.norm_eq_abs] at this

lemma le_of_norm_sub (f g : S → ℝ) (c : ℝ) (h : ‖f - g‖ ≤ c) (s : S) :
    f s ≤ g s + c ∧ g s ≤ f s + c := by
  have h1 := (abs_le_norm' (f - g) s).trans h
  rw [Pi.sub_apply, abs_le] at h1
  constructor <;> linarith [h1.1, h1.2]

lemma norm_sub_le_of [Nonempty S] (f g : S → ℝ) (c : ℝ)
    (h : ∀ s, f s ≤ g s + c ∧ g s ≤ f s + c) : ‖f - g‖ ≤ c := by
  refine (pi_norm_le_iff_of_nonempty _).mpr (fun s => ?_)
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [(h s).1, (h s).2]

/-! ## Monotone / shift bounds for `T_μ` and `T` -/

lemma qa_le (M : MDP S A) (s : S) (a : A) (J J' : S → ℝ) (d : ℝ) (h : ∀ j, J j ≤ J' j + d) :
    M.r s a + M.α * ∑ j, M.P s a j * J j ≤ M.r s a + M.α * ∑ j, M.P s a j * J' j + M.α * d := by
  have hP := (M.kernel s a).1
  have hk := (M.kernel s a).2
  have h1 : ∑ j, M.P s a j * J j ≤ ∑ j, M.P s a j * J' j + d := by
    calc ∑ j, M.P s a j * J j ≤ ∑ j, M.P s a j * (J' j + d) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (hP j))
      _ = ∑ j, M.P s a j * J' j + d := by
          rw [Finset.sum_congr rfl (fun j _ => mul_add (M.P s a j) (J' j) d),
            Finset.sum_add_distrib, ← Finset.sum_mul, hk, one_mul]
  have h2 := mul_le_mul_of_nonneg_left h1 M.α_pos.le
  rw [mul_add] at h2
  linarith

lemma pol_le (M : MDP S A) (μ : S → A) (J J' : S → ℝ) (d : ℝ) (h : ∀ j, J j ≤ J' j + d)
    (s : S) : policyOp M μ J s ≤ policyOp M μ J' s + M.α * d :=
  qa_le M s (μ s) J J' d h

lemma bell_le [Nonempty A] (M : MDP S A) (J J' : S → ℝ) (d : ℝ) (h : ∀ j, J j ≤ J' j + d)
    (s : S) : bellmanOp M J s ≤ bellmanOp M J' s + M.α * d := by
  rw [bell_eq, bell_eq]
  exact sup'_le_add _ _ _ _ _ (fun a _ => qa_le M s a J J' d h)

lemma pol_le_bell [Nonempty A] (M : MDP S A) (μ : S → A) (J : S → ℝ) (s : S) :
    policyOp M μ J s ≤ bellmanOp M J s := by
  rw [bell_eq]
  exact Finset.le_sup' (fun a => M.r s a + M.α * ∑ s', M.P s a s' * J s') (Finset.mem_univ (μ s))

lemma bell_iter_le [Nonempty A] (M : MDP S A) (n : ℕ) : ∀ (J J' : S → ℝ) (d : ℝ),
    (∀ j, J j ≤ J' j + d) → ∀ s, (bellmanOp M)^[n] J s ≤ (bellmanOp M)^[n] J' s + M.α ^ n * d := by
  induction n with
  | zero => intro J J' d h s; simpa using h s
  | succ n ih =>
    intro J J' d h s
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact bell_le M _ _ _ (ih J J' d h) s

lemma pol_iter_le (M : MDP S A) (μ : S → A) (n : ℕ) : ∀ (J J' : S → ℝ) (d : ℝ),
    (∀ j, J j ≤ J' j + d) → ∀ s,
      (policyOp M μ)^[n] J s ≤ (policyOp M μ)^[n] J' s + M.α ^ n * d := by
  induction n with
  | zero => intro J J' d h s; simpa using h s
  | succ n ih =>
    intro J J' d h s
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact pol_le M μ _ _ _ (ih J J' d h) s

lemma bell_iter_lip [Nonempty S] [Nonempty A] (M : MDP S A) (n : ℕ) (J J' : S → ℝ) :
    ‖(bellmanOp M)^[n] J - (bellmanOp M)^[n] J'‖ ≤ M.α ^ n * ‖J - J'‖ := by
  apply norm_sub_le_of
  intro s
  exact ⟨bell_iter_le M n J J' _ (fun j => (le_of_norm_sub J J' _ le_rfl j).1) s,
    bell_iter_le M n J' J _ (fun j => (le_of_norm_sub J J' _ le_rfl j).2) s⟩

lemma pol_iter_lip [Nonempty S] (M : MDP S A) (μ : S → A) (n : ℕ) (J J' : S → ℝ) :
    ‖(policyOp M μ)^[n] J - (policyOp M μ)^[n] J'‖ ≤ M.α ^ n * ‖J - J'‖ := by
  apply norm_sub_le_of
  intro s
  exact ⟨pol_iter_le M μ n J J' _ (fun j => (le_of_norm_sub J J' _ le_rfl j).1) s,
    pol_iter_le M μ n J' J _ (fun j => (le_of_norm_sub J J' _ le_rfl j).2) s⟩

lemma valueOf_fix' (M : MDP S A) (μ : S → A) : policyOp M μ (valueOf M μ) = valueOf M μ :=
  funext (fun s => (valueOf_fix M μ s).symm)

/-! ## Boxes `[0, 1/(1-α)]` -/

lemma val_bd (M : MDP S A) (μ : S → A) (s : S) :
    0 ≤ valueOf M μ s ∧ valueOf M μ s ≤ 1 / (1 - M.α) := by
  rw [valueOf_eq]
  constructor
  · exact tsum_nonneg (fun t => mul_nonneg (pow_nonneg M.α_pos.le t) (fR_bd M μ t s).1)
  · rw [one_div, ← tsum_geometric_of_lt_one M.α_pos.le M.α_lt_one]
    exact Summable.tsum_le_tsum
      (fun t => mul_le_of_le_one_right (pow_nonneg M.α_pos.le t) (fR_bd M μ t s).2)
      (hsum M μ s) (summable_geometric_of_lt_one M.α_pos.le M.α_lt_one)

lemma opt_bd [Nonempty A] (M : MDP S A) (s : S) :
    0 ≤ optValue M s ∧ optValue M s ≤ 1 / (1 - M.α) := by
  constructor
  · exact (val_bd M (fun _ => Classical.arbitrary A) s).1.trans (opt_ge M _ s)
  · exact Finset.sup'_le _ _ (fun μ _ => (val_bd M μ s).2)

lemma bell_box [Nonempty A] (M : MDP S A) (J : S → ℝ)
    (h : ∀ j, 0 ≤ J j ∧ J j ≤ 1 / (1 - M.α)) (s : S) :
    0 ≤ bellmanOp M J s ∧ bellmanOp M J s ≤ 1 / (1 - M.α) := by
  have h1a : (1 - M.α) ≠ 0 := by linarith [M.α_lt_one]
  have hB : 1 + M.α * (1 / (1 - M.α)) = 1 / (1 - M.α) := by field_simp; ring
  have hq : ∀ a, 0 ≤ M.r s a + M.α * ∑ j, M.P s a j * J j ∧
      M.r s a + M.α * ∑ j, M.P s a j * J j ≤ 1 / (1 - M.α) := by
    intro a
    have hP := (M.kernel s a).1
    have hk := (M.kernel s a).2
    have hs0 : 0 ≤ ∑ j, M.P s a j * J j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hP j) (h j).1)
    have hs1 : ∑ j, M.P s a j * J j ≤ 1 / (1 - M.α) := by
      calc ∑ j, M.P s a j * J j ≤ ∑ j, M.P s a j * (1 / (1 - M.α)) :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j).2 (hP j))
        _ = 1 / (1 - M.α) := by rw [← Finset.sum_mul, hk, one_mul]
    have := M.r_mem s a
    have h3 := mul_le_mul_of_nonneg_left hs1 M.α_pos.le
    have h4 := mul_nonneg M.α_pos.le hs0
    constructor
    · linarith [this.1]
    · linarith [this.2]
  rw [bell_eq]
  constructor
  · exact (hq (Classical.arbitrary A)).1.trans (Finset.le_sup'
      (fun a => M.r s a + M.α * ∑ s', M.P s a s' * J s') (Finset.mem_univ _))
  · exact Finset.sup'_le _ _ (fun a _ => (hq a).2)

lemma bell_iter_box [Nonempty A] (M : MDP S A) (n : ℕ) (J : S → ℝ)
    (h : ∀ j, 0 ≤ J j ∧ J j ≤ 1 / (1 - M.α)) (s : S) :
    0 ≤ (bellmanOp M)^[n] J s ∧ (bellmanOp M)^[n] J s ≤ 1 / (1 - M.α) := by
  induction n generalizing s with
  | zero => exact h s
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact bell_box M _ ih s

/-! ## The lower bound `T_μ x ≥ x - c ⟹ J^μ ≥ T_μ x - α c/(1-α)` -/

lemma val_lb [Nonempty S] (M : MDP S A) (μ : S → A) (x : S → ℝ) (c : ℝ)
    (h : ∀ s, x s - c ≤ policyOp M μ x s) (s : S) :
    policyOp M μ x s - M.α * (c / (1 - M.α)) ≤ valueOf M μ s := by
  obtain ⟨d, hd⟩ : ∃ d, d = Finset.univ.sup' Finset.univ_nonempty
      (fun s => x s - valueOf M μ s) := ⟨_, rfl⟩
  have hle : ∀ s, x s ≤ valueOf M μ s + d := fun s => by
    have := Finset.le_sup' (fun s => x s - valueOf M μ s) (Finset.mem_univ s)
    rw [← hd] at this
    linarith
  have hstep : ∀ s, x s - valueOf M μ s ≤ M.α * d + c := fun s => by
    have := pol_le M μ x (valueOf M μ) d hle s
    rw [← valueOf_fix M μ s] at this
    linarith [h s]
  have hdle : d ≤ M.α * d + c := by
    have : Finset.univ.sup' Finset.univ_nonempty (fun s => x s - valueOf M μ s) ≤
        M.α * d + c := Finset.sup'_le _ _ (fun s _ => hstep s)
    rwa [← hd] at this
  have h1a : 0 < 1 - M.α := by linarith [M.α_lt_one]
  have hd' : d ≤ c / (1 - M.α) := by
    rw [le_div_iff₀ h1a]
    nlinarith
  have := pol_le M μ x (valueOf M μ) (c / (1 - M.α)) (fun j => (hle j).trans (by linarith)) s
  rw [← valueOf_fix M μ s] at this
  linarith

/-! ## Eq. (15) -/

theorem eq15_core [Nonempty S] [Nonempty A] (M : MDP S A) (H : ℕ) (hH : 1 ≤ H) (εLA δk : ℝ)
    (Jk : S → ℝ) (μk μk1 : S → A)
    (hδ : ‖Jk - valueOf M μk‖ ≤ δk)
    (hLA : IsLookahead M H εLA Jk μk1) :
    ‖valueOf M μk1 - optValue M‖ ≤
      M.α ^ H * ‖valueOf M μk - optValue M‖ + (2 * M.α ^ H * δk + εLA) / (1 - M.α) := by
  obtain ⟨n, rfl⟩ : ∃ n, H = n + 1 := ⟨H - 1, by omega⟩
  unfold IsLookahead at hLA
  rw [Nat.add_sub_cancel] at hLA
  have hε := le_of_norm_sub _ _ _ hLA
  have h1 := le_of_norm_sub _ _ _ hδ
  -- T^n Jk ≤ T^n ν + α^n δ
  have h2 := bell_iter_le M n Jk (valueOf M μk) δk (fun j => (h1 j).1)
  have h3 := pol_le M μk1 _ _ _ h2
  have h4 := bell_iter_le M (n + 1) (valueOf M μk) Jk δk (fun j => (h1 j).2)
  have hνT : ∀ j, valueOf M μk j ≤ bellmanOp M (valueOf M μk) j + 0 := fun j => by
    have := pol_le_bell M μk (valueOf M μk) j
    rw [← valueOf_fix M μk j] at this
    linarith
  have h5 : ∀ s, (bellmanOp M)^[n] (valueOf M μk) s ≤ (bellmanOp M)^[n + 1] (valueOf M μk) s := by
    intro s
    have := bell_iter_le M n _ _ 0 hνT s
    rw [mul_zero, add_zero, ← Function.iterate_succ_apply] at this
    exact this
  have hV := le_of_norm_sub _ _ _ (le_refl ‖valueOf M μk - optValue M‖)
  have h6 := bell_iter_le M (n + 1) (optValue M) (valueOf M μk) _ (fun j => (hV j).2)
  rw [Function.iterate_fixed (opt_fix M)] at h6
  set c := 2 * M.α ^ (n + 1) * δk + εLA with hc
  have hpow : M.α * (M.α ^ n * δk) = M.α ^ (n + 1) * δk := by rw [pow_succ]; ring
  -- lower bound for T_{μ'} x
  have hx1 : ∀ s, (bellmanOp M)^[n + 1] (valueOf M μk) s - c ≤
      policyOp M μk1 ((bellmanOp M)^[n] (valueOf M μk)) s := by
    intro s
    have a1 := (hε s).1
    have a2 := h3 s
    have a3 := h4 s
    linarith
  have hx : ∀ s, (bellmanOp M)^[n] (valueOf M μk) s - c ≤
      policyOp M μk1 ((bellmanOp M)^[n] (valueOf M μk)) s := fun s => by
    linarith [hx1 s, h5 s]
  have hlb := val_lb M μk1 _ c hx
  have h1a : 0 < 1 - M.α := by linarith [M.α_lt_one]
  have hq : c / (1 - M.α) * (1 - M.α) = c := div_mul_cancel₀ c h1a.ne'
  apply norm_sub_le_of
  intro s
  constructor
  · have := opt_ge M μk1 s
    have hn : 0 ≤ M.α ^ (n + 1) * ‖valueOf M μk - optValue M‖ :=
      mul_nonneg (pow_nonneg M.α_pos.le _) (norm_nonneg _)
    have hc0 : 0 ≤ c / (1 - M.α) := by
      have hδ0 : 0 ≤ δk := (norm_nonneg _).trans hδ
      have hε0 : 0 ≤ εLA := (norm_nonneg _).trans hLA
      apply div_nonneg _ h1a.le
      rw [hc]
      have := pow_nonneg M.α_pos.le (n + 1)
      positivity
    linarith
  · have b1 := hlb s
    have b2 := hx1 s
    have b3 := h6 s
    linarith


end Aux_LA_TH1

open LookaheadAPI.LeastSquares FoundationsML.ReinforcementLearning Aux_LA_TH1 in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (H : ℕ) (hH : 1 ≤ H) (εLA δk : ℝ)
    (Jk : S → ℝ) (μk μk1 : S → A)
    (hδ : ‖Jk - valueOf M μk‖ ≤ δk)
    (hLA : IsLookahead M H εLA Jk μk1) :
    ‖valueOf M μk1 - optValue M‖ ≤
      M.α ^ H * ‖valueOf M μk - optValue M‖ + (2 * M.α ^ H * δk + εLA) / (1 - M.α) :=
  eq15_core M H hH εLA δk Jk μk μk1 hδ hLA
