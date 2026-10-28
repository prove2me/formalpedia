-- Prove2me | solution 1 for LookaheadAPI.LeastSquares.contraction_T
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:29:15.154634+00:00
-- url     : https://prove2.me/submissions/766b2512-15ea-4819-9ba8-988e9c301147

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP

namespace Aux_LA_CT
open FoundationsML.ReinforcementLearning LookaheadAPI.LeastSquares

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

end Aux_LA_CT

open LookaheadAPI.LeastSquares FoundationsML.ReinforcementLearning Aux_LA_CT in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (J : S → ℝ) :
    ‖bellmanOp M J - optValue M‖ ≤ M.α * ‖J - optValue M‖ := by
  have hfix := opt_fix M
  obtain ⟨c, hc⟩ : ∃ c, c = ‖J - optValue M‖ := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  have hb : ∀ j, |J j - optValue M j| ≤ c := fun j => by
    have := norm_le_pi_norm (J - optValue M) j
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    rw [hc]; exact this
  have hk : ∀ s a, ∑ s', M.P s a s' = 1 := fun s a => (M.kernel s a).2
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.α_pos.le hc0)).mpr (fun s => ?_)
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have hs : optValue M s = bellmanOp M (optValue M) s := (congrFun hfix s).symm
  rw [hs]
  have hQ : ∀ a, (M.r s a + M.α * ∑ s', M.P s a s' * J s') ≤
        (M.r s a + M.α * ∑ s', M.P s a s' * optValue M s') + M.α * c ∧
      (M.r s a + M.α * ∑ s', M.P s a s' * optValue M s') ≤
        (M.r s a + M.α * ∑ s', M.P s a s' * J s') + M.α * c := by
    intro a
    have hP := (M.kernel s a).1
    have hsum1 : ∑ j, M.P s a j * (J j - optValue M j) ≤ c := by
      calc ∑ j, M.P s a j * (J j - optValue M j) ≤ ∑ j, M.P s a j * c :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb j)) (hP j))
        _ = c := by rw [← Finset.sum_mul, hk, one_mul]
    have hsum2 : -c ≤ ∑ j, M.P s a j * (J j - optValue M j) := by
      calc -c = ∑ j, M.P s a j * (-c) := by rw [← Finset.sum_mul, hk, one_mul]
        _ ≤ ∑ j, M.P s a j * (J j - optValue M j) :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (by linarith [neg_abs_le (J j - optValue M j), hb j])
                (hP j))
    have h3 : ∑ j, M.P s a j * (J j - optValue M j) =
        ∑ j, M.P s a j * J j - ∑ j, M.P s a j * optValue M j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => mul_sub _ _ _)
    have h4 := mul_le_mul_of_nonneg_left hsum1 M.α_pos.le
    have h5 := mul_le_mul_of_nonneg_left hsum2 M.α_pos.le
    rw [h3, mul_sub] at h4 h5
    rw [mul_neg] at h5
    constructor
    · linarith
    · linarith
  rw [bell_eq, bell_eq, abs_sub_le_iff]
  constructor
  · have := sup'_le_add Finset.univ Finset.univ_nonempty
      (fun a => M.r s a + M.α * ∑ s', M.P s a s' * J s')
      (fun a => M.r s a + M.α * ∑ s', M.P s a s' * optValue M s') (M.α * c)
      (fun a _ => (hQ a).1)
    linarith
  · have := sup'_le_add Finset.univ Finset.univ_nonempty
      (fun a => M.r s a + M.α * ∑ s', M.P s a s' * optValue M s')
      (fun a => M.r s a + M.α * ∑ s', M.P s a s' * J s') (M.α * c)
      (fun a _ => (hQ a).2)
    linarith
