-- Prove2me | solution 1 for LookaheadAPI.LeastSquares.appendix_b_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:53:02.419416+00:00
-- url     : https://prove2.me/submissions/55aeab37-6c1d-4811-9b7f-9daf8dd315a7

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms
import Theorems.Thm_LookaheadAPI_LeastSquares_eq_6

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

lemma opNormInf_nonneg {m n : Type*} [Fintype m] [Fintype n] (L : Matrix m n ℝ) :
    0 ≤ opNormInf L := by
  unfold opNormInf
  letI := Matrix.linftyOpNormedAddCommGroup (m := m) (n := n) (α := ℝ)
  exact norm_nonneg L

lemma opNormInf_mulVec (L : Matrix S S ℝ) (v : S → ℝ) : ‖L *ᵥ v‖ ≤ opNormInf L * ‖v‖ := by
  unfold opNormInf
  letI := Matrix.linftyOpNormedAddCommGroup (m := S) (n := S) (α := ℝ)
  exact Matrix.linfty_opNorm_mulVec L v

lemma dFV_bdd {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) :
    BddAbove (Set.range fun k => opNormInf (lsOp Φ (D k))) :=
  ((Set.finite_range (fun E : Finset S => opNormInf (lsOp Φ E))).subset
    (by rintro _ ⟨k, rfl⟩; exact ⟨D k, rfl⟩)).bddAbove

lemma dFV_ge {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) (k : ℕ) :
    opNormInf (lsOp Φ (D k)) ≤ deltaFV Φ D :=
  le_ciSup (dFV_bdd Φ D) k

lemma dFV_nonneg {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) : 0 ≤ deltaFV Φ D :=
  (opNormInf_nonneg _).trans (dFV_ge Φ D 0)

lemma dApp_ge {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) (k : ℕ)
    (μ : S → A) : ‖lsOp Φ (D k) *ᵥ valueOf M μ - valueOf M μ‖ ≤ deltaApp M Φ D := by
  have hin : ∀ E : Finset S, BddAbove (Set.range fun μ : S → A =>
      ‖lsOp Φ E *ᵥ valueOf M μ - valueOf M μ‖) := fun E => (Set.finite_range _).bddAbove
  have hout : BddAbove (Set.range fun k => ⨆ μ : S → A,
      ‖lsOp Φ (D k) *ᵥ valueOf M μ - valueOf M μ‖) :=
    ((Set.finite_range (fun E : Finset S => ⨆ μ : S → A,
      ‖lsOp Φ E *ᵥ valueOf M μ - valueOf M μ‖)).subset
      (by rintro _ ⟨k, rfl⟩; exact ⟨D k, rfl⟩)).bddAbove
  exact le_ciSup_of_le hout k (le_ciSup (hin (D k)) μ)

lemma dApp_nonneg [Nonempty A] {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) : 0 ≤ deltaApp M Φ D :=
  (norm_nonneg _).trans (dApp_ge M Φ D 0 (fun _ => Classical.arbitrary A))

lemma tau_nonneg [Nonempty A] {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (εPE : ℝ) (hε : 0 ≤ εPE) : 0 ≤ tauLS M Φ D m H εPE := by
  unfold tauLS
  have h1a : 0 < 1 - M.α := by linarith [M.α_lt_one]
  have := dFV_nonneg Φ D
  have := dApp_nonneg M Φ D
  have := pow_nonneg M.α_pos.le m
  have := pow_nonneg M.α_pos.le (m + H - 1)
  positivity

lemma beta_nonneg {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S)
    (m H : ℕ) : 0 ≤ betaLS M Φ D m H :=
  mul_nonneg (pow_nonneg M.α_pos.le _) (dFV_nonneg Φ D)

theorem appB_step [Nonempty S] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (hH : 1 ≤ H) (εLA εPE : ℝ)
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hA1 : Assumption1 Φ D w εPE)
    (hrun : IsRunAlg2 M Φ D m H εLA J μ w θ) (k : ℕ) :
    ‖J (k + 1) - valueOf M (μ (k + 1))‖ ≤
      betaLS M Φ D m H * ‖J k - valueOf M (μ k)‖ + tauLS M Φ D m H εPE := by
  obtain ⟨h6a, h6b⟩ := eq_6 M Φ D m H εLA J μ w θ hA1.1 hrun k
  have hnr : noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1)) =
      (policyOp M (μ (k + 1)))^[m] ((bellmanOp M)^[H - 1] (J k)) + w (k + 1) := rfl
  set L := lsOp Φ (D k) with hL
  set ν := valueOf M (μ k)
  set ν' := valueOf M (μ (k + 1))
  set z := (bellmanOp M)^[H - 1] (J k)
  set y := (policyOp M (μ (k + 1)))^[m] z
  have hJ : J (k + 1) - ν' = L *ᵥ (y - ν') + L *ᵥ w (k + 1) + (L *ᵥ ν' - ν') := by
    rw [h6a, h6b, hnr, Matrix.mulVec_add, Matrix.mulVec_sub]; abel
  have hFV := dFV_ge Φ D k
  have hFV0 := dFV_nonneg Φ D
  have hApp := dApp_ge M Φ D k (μ (k + 1))
  have hw := hA1.2.2 (k + 1)
  have hy : ‖y - ν'‖ ≤ M.α ^ m * ‖z - ν'‖ := by
    have := pol_iter_lip M (μ (k + 1)) m z ν'
    rwa [Function.iterate_fixed (valueOf_fix' M (μ (k + 1)))] at this
  have hz : ‖z - ν'‖ ≤ M.α ^ (H - 1) * ‖J k - ν‖ + 1 / (1 - M.α) := by
    have e1 := bell_iter_lip M (H - 1) (J k) ν
    have e2 : ‖(bellmanOp M)^[H - 1] ν - ν'‖ ≤ 1 / (1 - M.α) := by
      apply norm_sub_le_of
      intro s
      have := bell_iter_box M (H - 1) ν (fun j => val_bd M (μ k) j) s
      have := val_bd M (μ (k + 1)) s
      constructor <;> linarith
    calc ‖z - ν'‖ ≤ ‖z - (bellmanOp M)^[H - 1] ν‖ + ‖(bellmanOp M)^[H - 1] ν - ν'‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add e1 e2
  have t1 : ‖L *ᵥ (y - ν')‖ ≤ deltaFV Φ D * (M.α ^ m * (M.α ^ (H - 1) * ‖J k - ν‖ +
      1 / (1 - M.α))) := by
    refine (opNormInf_mulVec L _).trans ?_
    refine mul_le_mul hFV (hy.trans ?_) (norm_nonneg _) hFV0
    exact mul_le_mul_of_nonneg_left hz (pow_nonneg M.α_pos.le m)
  have t2 : ‖L *ᵥ w (k + 1)‖ ≤ deltaFV Φ D * εPE :=
    (opNormInf_mulVec L _).trans (mul_le_mul hFV hw (norm_nonneg _) hFV0)
  have tri : ‖J (k + 1) - ν'‖ ≤ ‖L *ᵥ (y - ν')‖ + ‖L *ᵥ w (k + 1)‖ + ‖L *ᵥ ν' - ν'‖ := by
    rw [hJ]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  have hpow : M.α ^ (m + H - 1) = M.α ^ m * M.α ^ (H - 1) := by
    rw [← pow_add]; congr 1; omega
  have key : betaLS M Φ D m H * ‖J k - ν‖ + tauLS M Φ D m H εPE =
      deltaFV Φ D * (M.α ^ m * (M.α ^ (H - 1) * ‖J k - ν‖ + 1 / (1 - M.α))) +
        deltaFV Φ D * εPE + deltaApp M Φ D +
        deltaFV Φ D * (M.α ^ m * M.α ^ (H - 1)) / (1 - M.α) := by
    unfold betaLS tauLS
    rw [hpow]
    ring
  have h1a : 0 < 1 - M.α := by linarith [M.α_lt_one]
  have hlast : 0 ≤ deltaFV Φ D * (M.α ^ m * M.α ^ (H - 1)) / (1 - M.α) := by
    have := pow_nonneg M.α_pos.le m
    have := pow_nonneg M.α_pos.le (H - 1)
    positivity
  rw [key]
  linarith

theorem appB_full [Nonempty S] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (hH : 1 ≤ H) (εLA εPE : ℝ)
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hA1 : Assumption1 Φ D w εPE)
    (hrun : IsRunAlg2 M Φ D m H εLA J μ w θ) :
    (∀ k : ℕ, ‖J (k + 1) - valueOf M (μ (k + 1))‖ ≤
      betaLS M Φ D m H * ‖J k - valueOf M (μ k)‖ + tauLS M Φ D m H εPE) ∧
    (∀ k : ℕ, ‖J k - valueOf M (μ k)‖ ≤
      betaLS M Φ D m H ^ k * ‖J 0 - valueOf M (μ 0)‖ +
        ∑ i ∈ Finset.range k, betaLS M Φ D m H ^ i * tauLS M Φ D m H εPE) ∧
    (betaLS M Φ D m H < 1 → ∀ k : ℕ, ‖J k - valueOf M (μ k)‖ ≤
      betaLS M Φ D m H ^ k * ‖J 0 - valueOf M (μ 0)‖ +
        tauLS M Φ D m H εPE / (1 - betaLS M Φ D m H)) := by
  have hstep := appB_step M Φ D m H hH εLA εPE J μ w θ hA1 hrun
  have hb0 := beta_nonneg M Φ D m H
  have ht0 := tau_nonneg M Φ D m H εPE hA1.2.1.le
  set β := betaLS M Φ D m H
  set τ := tauLS M Φ D m H εPE
  have hiter : ∀ k : ℕ, ‖J k - valueOf M (μ k)‖ ≤
      β ^ k * ‖J 0 - valueOf M (μ 0)‖ + ∑ i ∈ Finset.range k, β ^ i * τ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine (hstep k).trans ?_
      have h1 := mul_le_mul_of_nonneg_left ih hb0
      have h2 : β * (β ^ k * ‖J 0 - valueOf M (μ 0)‖ + ∑ i ∈ Finset.range k, β ^ i * τ) + τ =
          β ^ (k + 1) * ‖J 0 - valueOf M (μ 0)‖ + ∑ i ∈ Finset.range (k + 1), β ^ i * τ := by
        rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
        simp only [pow_succ, pow_zero, one_mul]
        ring_nf
      linarith
  refine ⟨hstep, hiter, fun hb1 k => (hiter k).trans ?_⟩
  have h1b : 0 < 1 - β := by linarith
  have hg : ∑ i ∈ Finset.range k, β ^ i * τ ≤ τ / (1 - β) := by
    rw [← Finset.sum_mul, le_div_iff₀ h1b]
    have hm := mul_neg_geom_sum β k
    have : 0 ≤ β ^ k := pow_nonneg hb0 k
    calc (∑ i ∈ Finset.range k, β ^ i) * τ * (1 - β)
        = ((1 - β) * ∑ i ∈ Finset.range k, β ^ i) * τ := by ring
      _ = (1 - β ^ k) * τ := by rw [hm]
      _ ≤ τ := by nlinarith
  linarith


end Aux_LA_TH1

open LookaheadAPI.LeastSquares FoundationsML.ReinforcementLearning Aux_LA_TH1 in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (hH : 1 ≤ H) (εLA εPE : ℝ)
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hA1 : Assumption1 Φ D w εPE)
    (hrun : IsRunAlg2 M Φ D m H εLA J μ w θ) :
    (∀ k : ℕ, ‖J (k + 1) - valueOf M (μ (k + 1))‖ ≤
      betaLS M Φ D m H * ‖J k - valueOf M (μ k)‖ + tauLS M Φ D m H εPE) ∧
    (∀ k : ℕ, ‖J k - valueOf M (μ k)‖ ≤
      betaLS M Φ D m H ^ k * ‖J 0 - valueOf M (μ 0)‖ +
        ∑ i ∈ Finset.range k, betaLS M Φ D m H ^ i * tauLS M Φ D m H εPE) ∧
    (betaLS M Φ D m H < 1 → ∀ k : ℕ, ‖J k - valueOf M (μ k)‖ ≤
      betaLS M Φ D m H ^ k * ‖J 0 - valueOf M (μ 0)‖ +
        tauLS M Φ D m H εPE / (1 - betaLS M Φ D m H)) :=
  appB_full M Φ D m H hH εLA εPE J μ w θ hA1 hrun
