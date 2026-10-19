-- Prove2me | solution 1 for MDPFinance.OptimalStopping.theorem_10_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T21:19:09.775263+00:00
-- url     : https://prove2.me/submissions/fe70b277-8c91-4242-a69f-e8212e3a9a37

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace HSAux
open MDPFinance.OptimalStopping

variable (H : HouseSelling)

lemma cyl_eq (m : ℕ) : ∀ (B : ℕ → Set ℝ) (y : ℝ),
    H.toProblem.cyl m B y = ∏ i ∈ Finset.range m, H.Q (B i) := by
  induction m with
  | zero => intro B y; simp [StationaryProblem.cyl]
  | succ m ih =>
    intro B y
    simp only [StationaryProblem.cyl, ih]
    rw [setLIntegral_const, Finset.prod_range_succ']
    simp [HouseSelling.toProblem, mul_comm]

variable {H}
variable {Pr : ℝ → Measure (ℕ → ℝ)} (hPr : H.toProblem.IsPathLaw Pr)
include hPr

lemma isProb (x : ℝ) : IsProbabilityMeasure (Pr x) := hPr.1 x

lemma box (x : ℝ) (m : ℕ) (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    Pr x {w : ℕ → ℝ | ∀ i ≤ m, w i ∈ B i}
      = (B 0).indicator (fun _ => ∏ i ∈ Finset.range m, H.Q (B (i + 1))) x := by
  rw [hPr.2 x m B hB]
  simp only [cyl_eq]

/-- the initial coordinate is `x` almost surely -/
lemma ae_zero (x : ℝ) : ∀ᵐ w ∂(Pr x), w 0 = x := by
  have h := box hPr x 0 (fun i => if i = 0 then ({x}ᶜ : Set ℝ) else Set.univ)
    (fun i => by split_ifs <;> simp [MeasurableSet.singleton])
  simp only [Set.indicator, if_true, Set.mem_compl_iff, Set.mem_singleton_iff,
    not_true_eq_false, if_false] at h
  rw [ae_iff]
  refine le_antisymm (le_trans (measure_mono ?_) h.le) (zero_le')
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro i hi
  have : i = 0 := by omega
  subst this
  simpa using hw

/-- marginal of coordinate `j+1` is `Q` -/
lemma map_coord (x : ℝ) (j : ℕ) : (Pr x).map (fun w => w (j + 1)) = H.Q := by
  haveI := isProb hPr x
  ext T hT
  rw [Measure.map_apply (by fun_prop : Measurable fun w : ℕ → ℝ => w (j + 1)) hT]
  have h := box hPr x (j + 1) (fun i => if i = j + 1 then T else Set.univ)
    (fun i => by split_ifs <;> simp [hT])
  have hs : {w : ℕ → ℝ | ∀ i ≤ j + 1, w i ∈ (fun i => if i = j + 1 then T else Set.univ) i}
      = (fun w : ℕ → ℝ => w (j + 1)) ⁻¹' T := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro hw; simpa using hw (j + 1) le_rfl
    · intro hw i _; split_ifs with h <;> simp_all
  rw [hs] at h
  rw [h]
  simp only [Set.indicator, show (0 : ℕ) ≠ j + 1 by omega, if_false, Set.mem_univ, if_true]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    haveI := H.Q_prob
    simp [hb]
  · intro h; simp at h

lemma map_coord' (x : ℝ) (j : ℕ) (hj : 1 ≤ j) : (Pr x).map (fun w => w j) = H.Q := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact map_coord hPr x i

/-- the measures of the finite-dimensional law -/
noncomputable def mus (x : ℝ) (n : ℕ) (i : Fin (n + 1)) : Measure ℝ :=
  if i = 0 then Measure.dirac x else H.Q

omit hPr in
lemma mus_prob (x : ℝ) (n : ℕ) (i : Fin (n + 1)) : IsProbabilityMeasure (mus (H := H) x n i) := by
  unfold mus; haveI := H.Q_prob; split_ifs <;> infer_instance

/-- projection onto the first `n+1` coordinates -/
def proj (n : ℕ) (w : ℕ → ℝ) : Fin (n + 1) → ℝ := fun i => w i

omit hPr in
lemma proj_meas (n : ℕ) : Measurable (proj n) := measurable_pi_lambda _ (fun i => measurable_pi_apply _)

lemma fdd (x : ℝ) (n : ℕ) : (Pr x).map (proj n) = Measure.pi (mus (H := H) x n) := by
  haveI := fun i => mus_prob (H := H) x n i
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (proj_meas n) (MeasurableSet.univ_pi hs)]
  let B : ℕ → Set ℝ := fun i => if h : i ≤ n then s ⟨i, by omega⟩ else Set.univ
  have hB : ∀ i, MeasurableSet (B i) := fun i => by
    simp only [B]; split_ifs <;> simp [hs]
  have hset : proj n ⁻¹' Set.univ.pi s = {w : ℕ → ℝ | ∀ i ≤ n, w i ∈ B i} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_univ_pi, proj, Set.mem_setOf_eq, B]
    constructor
    · intro h i hi; rw [dif_pos hi]; exact h ⟨i, by omega⟩
    · intro h i; have := h i.1 (by omega); rw [dif_pos (by omega)] at this; exact this
  rw [hset, box hPr x n B hB, Fin.prod_univ_succ]
  simp only [mus, if_pos rfl, Fin.succ_ne_zero, if_false, if_true]
  rw [Measure.dirac_apply' _ (hs 0)]
  have h0 : B 0 = s 0 := by simp [B]
  rw [h0]
  by_cases hx : x ∈ s 0
  · simp only [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
    rw [← Fin.prod_univ_eq_prod_range (fun i => H.Q (B (i + 1)))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hi' : (i : ℕ) + 1 ≤ n := by omega
    simp only [B, dif_pos hi']
    rfl
  · simp [Set.indicator_of_notMem hx]

/-- independence of the past `w 0, …, w k` and the next coordinate `w (k+1)` -/
lemma indep (x : ℝ) (k : ℕ) :
    IndepFun (fun w : ℕ → ℝ => w (k + 1)) (proj k) (Pr x) := by
  haveI := isProb hPr x
  haveI := fun i => mus_prob (H := H) x (k + 1) i
  haveI := fun i => mus_prob (H := H) x k i
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop : Measurable fun w : ℕ → ℝ => w (k + 1)).aemeasurable
    (proj_meas k).aemeasurable, map_coord hPr, fdd hPr]
  have hmp := measurePreserving_piFinSuccAbove (mus (H := H) x (k + 1)) (Fin.last (k + 1))
  have hcomp : (fun w : ℕ → ℝ => (w (k + 1), proj k w))
      = (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last (k + 1))) ∘ proj (k + 1) := by
    funext w
    simp [MeasurableEquiv.piFinSuccAbove, proj, Fin.insertNthEquiv, Fin.removeNth]
    rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.measurable _) (proj_meas _), fdd hPr, hmp.map_eq]
  congr 1
  congr 1
  funext j
  simp only [mus, Fin.succAbove_last]
  congr 1
  exact propext ⟨fun h => Fin.ext (by simpa using congrArg Fin.val h),
    fun h => by subst h; rfl⟩

end HSAux

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace HSAux
open MDPFinance.OptimalStopping

lemma stop_set {τ : (ℕ → ℝ) → ℕ∞} (hτ : IsStopTime τ) (k : ℕ) :
    ∃ T : Set (Fin (k + 1) → ℝ), MeasurableSet T ∧ {w | τ w ≤ (k : ℕ∞)} = proj k ⁻¹' T := by
  obtain ⟨T, hT, he⟩ := (MeasurableSpace.measurableSet_comap).1 (hτ k)
  exact ⟨T, hT, he.symm⟩

lemma stop_meas {τ : (ℕ → ℝ) → ℕ∞} (hτ : IsStopTime τ) (k : ℕ) :
    MeasurableSet {w | τ w ≤ (k : ℕ∞)} := by
  obtain ⟨T, hT, he⟩ := stop_set hτ k
  rw [he]; exact proj_meas k hT

lemma tau_meas {τ : (ℕ → ℝ) → ℕ∞} (hτ : IsStopTime τ) : Measurable τ := by
  refine measurable_to_countable' (fun e => ?_)
  induction e using ENat.recTopCoe with
  | top =>
    have : τ ⁻¹' {⊤} = (⋃ n : ℕ, {w | τ w ≤ (n : ℕ∞)})ᶜ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_setOf_eq, not_exists, not_le]
      constructor
      · intro h n; rw [h]; exact ENat.coe_lt_top n
      · intro h
        by_contra hne
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
        exact absurd (h n) (by rw [← hn]; exact lt_irrefl _)
    rw [this]
    exact (MeasurableSet.iUnion (fun n => stop_meas hτ n)).compl
  | coe n =>
    cases n with
    | zero =>
      have : τ ⁻¹' {((0 : ℕ) : ℕ∞)} = {w | τ w ≤ ((0 : ℕ) : ℕ∞)} := by
        ext w; simp
      rw [this]; exact stop_meas hτ 0
    | succ n =>
      have : τ ⁻¹' {((n + 1 : ℕ) : ℕ∞)} =
          {w | τ w ≤ ((n + 1 : ℕ) : ℕ∞)} \ {w | τ w ≤ (n : ℕ∞)} := by
        ext w
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq, not_le]
        constructor
        · intro h; rw [h]; exact ⟨le_rfl, by exact_mod_cast Nat.lt_succ_self n⟩
        · rintro ⟨h1, h2⟩
          induction h : τ w using ENat.recTopCoe with
          | top => rw [h] at h1; exact absurd h1 (by simp)
          | coe m =>
            rw [h] at h1 h2
            have h1' : m ≤ n + 1 := by exact_mod_cast h1
            have h2' : n < m := by exact_mod_cast h2
            have : m = n + 1 := by omega
            rw [this]
      rw [this]; exact (stop_meas hτ _).diff (stop_meas hτ _)

/-- the reward as a function of the path and the value of the stopping time -/
noncomputable def G (H : HouseSelling) (p : (ℕ → ℝ) × ℕ∞) : ℝ :=
  match p.2 with
  | (m : ℕ) => (∑ k ∈ Finset.range m, H.beta ^ k * (-H.c)) + H.beta ^ m * p.1 m
  | ⊤ => 0

lemma reward_eq (H : HouseSelling) (τ : (ℕ → ℝ) → ℕ∞) (w : ℕ → ℝ) :
    H.toProblem.reward τ w = G H (w, τ w) := by
  unfold StationaryProblem.reward G
  rcases τ w with _ | m <;> rfl

lemma reward_coe (H : HouseSelling) (τ : (ℕ → ℝ) → ℕ∞) (w : ℕ → ℝ) (n : ℕ)
    (h : τ w = (n : ℕ∞)) :
    H.toProblem.reward τ w = (∑ k ∈ Finset.range n, H.beta ^ k * (-H.c)) + H.beta ^ n * w n := by
  rw [reward_eq, h]; rfl

lemma reward_meas (H : HouseSelling) {τ : (ℕ → ℝ) → ℕ∞} (hτ : IsStopTime τ) :
    Measurable (fun w => H.toProblem.reward τ w) := by
  have hG : Measurable (G H) := by
    refine measurable_from_prod_countable_left (fun e => ?_)
    induction e using ENat.recTopCoe with
    | top => exact measurable_const
    | coe m =>
      show Measurable (fun w : ℕ → ℝ =>
        (∑ k ∈ Finset.range m, H.beta ^ k * (-H.c)) + H.beta ^ m * w m)
      fun_prop
  have : (fun w => H.toProblem.reward τ w) = G H ∘ (fun w => (w, τ w)) := by
    funext w; exact reward_eq H τ w
  rw [this]
  exact hG.comp (measurable_id.prodMk (tau_meas hτ))

/-! ## hitting times -/

lemma hit_le_iff (S : Set ℝ) (w : ℕ → ℝ) (n : ℕ) :
    hitTime S w ≤ (n : ℕ∞) ↔ ∃ k ≤ n, w k ∈ S := by
  unfold hitTime
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have : ((n + 1 : ℕ) : ℕ∞) ≤ sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S}) := by
      refine le_sInf ?_
      rintro _ ⟨k, hk, rfl⟩
      have : n < k := by
        by_contra hkn; push Not at hkn; exact hne k hkn hk
      show ((n + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞)
      exact_mod_cast this
    have := this.trans h
    have : n + 1 ≤ n := by exact_mod_cast this
    omega
  · rintro ⟨k, hk, hS⟩
    have h1 : sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S}) ≤ (k : ℕ∞) :=
      sInf_le ⟨k, hS, rfl⟩
    exact h1.trans (by exact_mod_cast hk)

lemma hit_isStop (S : Set ℝ) (hS : MeasurableSet S) : IsStopTime (hitTime S) := by
  intro n
  have : {w : ℕ → ℝ | hitTime S w ≤ (n : ℕ∞)}
      = (fun w : ℕ → ℝ => fun i : Fin (n + 1) => w i) ⁻¹' (⋃ i : Fin (n + 1), {f | f i ∈ S}) := by
    ext w
    simp only [Set.mem_setOf_eq, hit_le_iff, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨⟨k, by omega⟩, h⟩
    · rintro ⟨i, h⟩; exact ⟨i, by omega, h⟩
  rw [this]
  refine MeasurableSet.preimage ?_ (comap_measurable _)
  exact MeasurableSet.iUnion (fun i => (measurable_pi_apply i) hS)

lemma hit_coe (S : Set ℝ) (w : ℕ → ℝ) (n : ℕ) (h : hitTime S w = (n : ℕ∞)) :
    w n ∈ S ∧ ∀ k < n, w k ∉ S := by
  have hle : hitTime S w ≤ (n : ℕ∞) := h.le
  obtain ⟨k, hk, hkS⟩ := (hit_le_iff S w n).1 hle
  have hall : ∀ k < n, w k ∉ S := by
    intro j hj hjS
    have : hitTime S w ≤ (j : ℕ∞) := (hit_le_iff S w j).2 ⟨j, le_rfl, hjS⟩
    rw [h] at this
    have : n ≤ j := by exact_mod_cast this
    omega
  refine ⟨?_, hall⟩
  rcases lt_or_eq_of_le hk with hlt | heq
  · exact absurd hkS (hall k hlt)
  · rw [← heq]; exact hkS

end HSAux

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace HSAux
open MDPFinance.OptimalStopping

variable {H : HouseSelling}

lemma Q_ae : ∀ᵐ y ∂H.Q, y ∈ Set.Icc H.m H.M := by
  rw [ae_iff]
  refine le_antisymm (le_trans (measure_mono ?_) H.Q_supp.le) zero_le
  intro y hy
  simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le] at hy ⊢
  exact hy

lemma v_bound (t y : ℝ) (hy : y ∈ Set.Icc H.m H.M) : |max y t| ≤ |t| + H.M := by
  have hm := H.m_pos
  rcases le_total y t with h | h
  · rw [max_eq_right h]; linarith [hy.1, hy.2, abs_nonneg t]
  · rw [max_eq_left h, abs_of_pos (by linarith [hy.1])]; linarith [hy.2, abs_nonneg t]

lemma v_int (t : ℝ) : Integrable (fun y => max y t) H.Q := by
  haveI := H.Q_prob
  refine Integrable.of_bound (by fun_prop : Measurable fun y : ℝ => max y t).aestronglyMeasurable
    (|t| + H.M) ?_
  filter_upwards [Q_ae] with y hy
  rw [Real.norm_eq_abs]; exact v_bound t y hy

variable {Pr : ℝ → Measure (ℕ → ℝ)} (hPr : H.toProblem.IsPathLaw Pr)

include hPr in
lemma ae_good (x : ℝ) (hx : x ∈ H.E) :
    ∀ᵐ w ∂(Pr x), w 0 = x ∧ ∀ j, w j ∈ Set.Icc H.m H.M := by
  have h0 := ae_zero hPr x
  have hj : ∀ j, ∀ᵐ w ∂(Pr x), w j ∈ Set.Icc H.m H.M := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · filter_upwards [h0] with w hw; rw [hw]; exact hx
    · have hm : (Pr x).map (fun w => w j) = H.Q := map_coord' hPr x j hj
      have : ∀ᵐ y ∂((Pr x).map (fun w => w j)), y ∈ Set.Icc H.m H.M := by rw [hm]; exact Q_ae
      exact ae_of_ae_map (by fun_prop : Measurable fun w : ℕ → ℝ => w j).aemeasurable this
  filter_upwards [h0, ae_all_iff.2 hj] with w h1 h2 using ⟨h1, h2⟩

/-- indicator of `{k < τ}` -/
noncomputable def ind (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) : (ℕ → ℝ) → ℝ :=
  ({w | τ w ≤ (k : ℕ∞)}ᶜ).indicator (fun _ => 1)

lemma ind_of_lt (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) (w : ℕ → ℝ) (n : ℕ) (h : τ w = n) (hk : k < n) :
    ind τ k w = 1 := by
  unfold ind
  rw [Set.indicator_of_mem]
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, h, not_le]
  exact_mod_cast hk

lemma ind_of_ge (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) (w : ℕ → ℝ) (n : ℕ) (h : τ w = n) (hk : n ≤ k) :
    ind τ k w = 0 := by
  unfold ind
  rw [Set.indicator_of_notMem]
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, h, not_not]
  exact_mod_cast hk

lemma ind_nonneg (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) (w : ℕ → ℝ) : 0 ≤ ind τ k w := by
  unfold ind; exact Set.indicator_nonneg (fun _ _ => zero_le_one) w

lemma ind_le_one (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) (w : ℕ → ℝ) : ind τ k w ≤ 1 := by
  unfold ind; exact Set.indicator_le_self' (fun _ _ => zero_le_one) w

lemma ind_meas {τ : (ℕ → ℝ) → ℕ∞} (hτ : IsStopTime τ) (k : ℕ) : Measurable (ind τ k) :=
  measurable_const.indicator (stop_meas hτ k).compl

section core
variable (H) (t A : ℝ)

noncomputable def aT (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) (w : ℕ → ℝ) : ℝ :=
  ind τ k w * (H.beta ^ (k + 1) * (max (w (k + 1)) t - A))

noncomputable def bT (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) (w : ℕ → ℝ) : ℝ :=
  ind τ k w * (H.beta ^ k * (t - max (w k) t))

noncomputable def FT (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) (w : ℕ → ℝ) : ℝ :=
  aT H t A τ k w + bT H t τ k w

end core

lemma beta_pos : 0 < H.beta := H.beta_mem.1
lemma beta_lt : H.beta < 1 := H.beta_mem.2

lemma pow_succ_le (k : ℕ) : H.beta ^ (k + 1) ≤ H.beta ^ k :=
  pow_le_pow_of_le_one beta_pos.le beta_lt.le (Nat.le_succ k)

lemma FT_bound (t A : ℝ) (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) (w : ℕ → ℝ)
    (hw : ∀ j, w j ∈ Set.Icc H.m H.M) :
    |FT H t A τ k w| ≤ H.beta ^ k * (3 * |t| + 2 * H.M + |A|) := by
  have hb := pow_succ_le (H := H) k
  have hbk : 0 ≤ H.beta ^ k := pow_nonneg beta_pos.le k
  have hb1 : 0 ≤ H.beta ^ (k + 1) := pow_nonneg beta_pos.le (k + 1)
  have hv1 := v_bound t _ (hw (k + 1))
  have hv0 := v_bound t _ (hw k)
  have hi0 := ind_nonneg τ k w
  have hi1 := ind_le_one τ k w
  unfold FT aT bT
  have e1 : |ind τ k w * (H.beta ^ (k + 1) * (max (w (k + 1)) t - A))|
      ≤ H.beta ^ k * (|t| + H.M + |A|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hi0, abs_of_nonneg hb1]
    have : |max (w (k + 1)) t - A| ≤ |t| + H.M + |A| := by
      calc _ ≤ |max (w (k + 1)) t| + |A| := abs_sub _ _
        _ ≤ _ := by linarith
    calc ind τ k w * (H.beta ^ (k + 1) * |max (w (k + 1)) t - A|)
        ≤ 1 * (H.beta ^ k * (|t| + H.M + |A|)) := by
          apply mul_le_mul hi1 _ (by positivity) zero_le_one
          exact mul_le_mul hb this (abs_nonneg _) hbk
      _ = _ := one_mul _
  have e2 : |ind τ k w * (H.beta ^ k * (t - max (w k) t))| ≤ H.beta ^ k * (2 * |t| + H.M) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hi0, abs_of_nonneg hbk]
    have : |t - max (w k) t| ≤ 2 * |t| + H.M := by
      calc _ ≤ |t| + |max (w k) t| := abs_sub _ _
        _ ≤ _ := by linarith
    calc ind τ k w * (H.beta ^ k * |t - max (w k) t|)
        ≤ 1 * (H.beta ^ k * (2 * |t| + H.M)) := by
          apply mul_le_mul hi1 _ (by positivity) zero_le_one
          exact mul_le_mul le_rfl this (abs_nonneg _) hbk
      _ = _ := one_mul _
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ H.beta ^ k * (|t| + H.M + |A|) + H.beta ^ k * (2 * |t| + H.M) := add_le_add e1 e2
    _ = _ := by ring

lemma FT_meas (t A : ℝ) {τ : (ℕ → ℝ) → ℕ∞} (hτ : IsStopTime τ) (k : ℕ) :
    Measurable (FT H t A τ k) := by
  have hi := ind_meas hτ k
  unfold FT aT bT
  fun_prop

include hPr in
lemma aT_int (x t A : ℝ) (hA : A = ∫ y, max y t ∂H.Q) {τ : (ℕ → ℝ) → ℕ∞} (hτ : IsStopTime τ)
    (k : ℕ) : ∫ w, aT H t A τ k w ∂(Pr x) = 0 := by
  haveI := isProb hPr x
  haveI := H.Q_prob
  obtain ⟨T, hT, he⟩ := stop_set hτ k
  let φ : (Fin (k + 1) → ℝ) → ℝ := (Tᶜ).indicator (fun _ => 1)
  let ψ : ℝ → ℝ := fun y => H.beta ^ (k + 1) * (max y t - A)
  have hφ : Measurable φ := measurable_const.indicator hT.compl
  have hψ : Measurable ψ := by fun_prop
  have heq : aT H t A τ k = fun w => φ (proj k w) * ψ (w (k + 1)) := by
    funext w
    unfold aT ind
    congr 1
    simp only [φ, Set.indicator]
    have : (w ∈ {w | τ w ≤ (k : ℕ∞)}ᶜ) ↔ (proj k w ∈ Tᶜ) := by
      rw [he]; rfl
    by_cases h : proj k w ∈ Tᶜ
    · rw [if_pos (this.2 h), if_pos h]
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
  have hind : IndepFun (φ ∘ proj k) (ψ ∘ fun w : ℕ → ℝ => w (k + 1)) (Pr x) :=
    ((indep hPr x k).comp hψ hφ).symm
  rw [heq]
  have := hind.integral_fun_mul_eq_mul_integral (hφ.comp (proj_meas k)).aestronglyMeasurable
    (hψ.comp (by fun_prop : Measurable fun w : ℕ → ℝ => w (k + 1))).aestronglyMeasurable
  simp only [Function.comp] at this
  rw [this]
  have h2 : ∫ w, ψ (w (k + 1)) ∂(Pr x) = 0 := by
    rw [← integral_map (by fun_prop : Measurable fun w : ℕ → ℝ => w (k + 1)).aemeasurable
      hψ.aestronglyMeasurable, map_coord hPr]
    simp only [ψ]
    rw [integral_const_mul, integral_sub (v_int t) (integrable_const A), integral_const, ← hA]
    simp
  rw [h2, mul_zero]

lemma bT_nonpos (t : ℝ) (τ : (ℕ → ℝ) → ℕ∞) (k : ℕ) (w : ℕ → ℝ) : bT H t τ k w ≤ 0 := by
  unfold bT
  apply mul_nonpos_of_nonneg_of_nonpos (ind_nonneg τ k w)
  apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg beta_pos.le k)
  linarith [le_max_right (w k) t]

/-- pathwise telescoping identity -/
lemma tele (x t A : ℝ) (ht : -H.c + H.beta * A = t) (τ : (ℕ → ℝ) → ℕ∞) (w : ℕ → ℝ) (n : ℕ)
    (h : τ w = n) (h0 : w 0 = x) :
    max x t + ∑' k, FT H t A τ k w
      = (∑ k ∈ Finset.range n, H.beta ^ k * (-H.c)) + H.beta ^ n * max (w n) t := by
  rw [tsum_eq_sum (s := Finset.range n)]
  · have : ∀ k ∈ Finset.range n, FT H t A τ k w =
        (H.beta ^ (k + 1) * max (w (k + 1)) t - H.beta ^ k * max (w k) t)
          + H.beta ^ k * (-H.c) := by
      intro k hk
      unfold FT aT bT
      rw [ind_of_lt τ k w n h (Finset.mem_range.1 hk)]
      have : -H.c = t - H.beta * A := by linarith
      rw [this]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib,
      Finset.sum_range_sub (fun k => H.beta ^ k * max (w k) t), h0]
    ring
  · intro k hk
    unfold FT aT bT
    rw [ind_of_ge τ k w n h (by simpa using hk)]
    ring

lemma geom_le (N : ℕ) : ∑ k ∈ Finset.range N, H.beta ^ k ≤ (1 - H.beta)⁻¹ := by
  rw [← tsum_geometric_of_lt_one beta_pos.le beta_lt]
  exact Summable.sum_le_tsum _ (fun k _ => pow_nonneg beta_pos.le k)
    (summable_geometric_of_lt_one beta_pos.le beta_lt)

include hPr in
/-- the main estimate: for a stopping time `τ` finite a.s., `∫ f = v x + lim Σ ∫ bT`, where `f`
is the stopped value process -/
theorem core (x : ℝ) (hx : x ∈ H.E) (t A : ℝ) (hA : A = ∫ y, max y t ∂H.Q)
    (ht : -H.c + H.beta * A = t) {τ : (ℕ → ℝ) → ℕ∞} (hτ : IsStopTime τ)
    (hfin : Pr x {w | τ w = ⊤} = 0) :
    Integrable (fun w => H.toProblem.reward τ w) (Pr x) ∧
    ∃ f : (ℕ → ℝ) → ℝ, Integrable f (Pr x) ∧
      (∀ᵐ w ∂(Pr x), ∀ n : ℕ, τ w = n →
        f w = (∑ k ∈ Finset.range n, H.beta ^ k * (-H.c)) + H.beta ^ n * max (w n) t) ∧
      (∀ᵐ w ∂(Pr x), H.toProblem.reward τ w ≤ f w) ∧
      ∫ w, f w ∂(Pr x) ≤ max x t ∧
      ((∀ k, ∀ᵐ w ∂(Pr x), bT H t τ k w = 0) → ∫ w, f w ∂(Pr x) = max x t) := by
  haveI := isProb hPr x
  set K := 3 * |t| + 2 * H.M + |A| with hK
  have hKnn : 0 ≤ K := by
    have := H.m_pos; have := H.m_lt_M; have := abs_nonneg t; have := abs_nonneg A; linarith
  have hgood := ae_good hPr x hx
  have hfin' : ∀ᵐ w ∂(Pr x), τ w ≠ ⊤ := by
    rw [ae_iff]; simpa using hfin
  have hb0 := beta_pos (H := H)
  have hb1 := beta_lt (H := H)
  -- summability
  have hsum : ∀ w, (∀ j, w j ∈ Set.Icc H.m H.M) → Summable (fun k => FT H t A τ k w) := by
    intro w hw
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hb0.le hb1).mul_right K) ?_
    intro k; rw [Real.norm_eq_abs]; exact FT_bound t A τ k w hw
  let f : (ℕ → ℝ) → ℝ := fun w => max x t + ∑' k, FT H t A τ k w
  let S : ℕ → (ℕ → ℝ) → ℝ := fun N w => max x t + ∑ k ∈ Finset.range N, FT H t A τ k w
  have hSmeas : ∀ N, Measurable (S N) := by
    intro N
    exact measurable_const.add (Finset.measurable_sum _ (fun k _ => FT_meas t A hτ k))
  set B := |max x t| + K * (1 - H.beta)⁻¹ with hB
  have hSbound : ∀ N, ∀ w, (∀ j, w j ∈ Set.Icc H.m H.M) → |S N w| ≤ B := by
    intro N w hw
    simp only [S]
    calc |max x t + ∑ k ∈ Finset.range N, FT H t A τ k w|
        ≤ |max x t| + |∑ k ∈ Finset.range N, FT H t A τ k w| := abs_add_le _ _
      _ ≤ |max x t| + ∑ k ∈ Finset.range N, H.beta ^ k * K := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum (fun k _ => FT_bound t A τ k w hw))
      _ ≤ B := by
          rw [← Finset.sum_mul, hB, mul_comm]
          gcongr
          exact geom_le N
  have hlim : ∀ᵐ w ∂(Pr x), Tendsto (fun N => S N w) atTop (𝓝 (f w)) := by
    filter_upwards [hgood] with w hw
    exact ((hsum w hw.2).hasSum.tendsto_sum_nat).const_add _
  have hfmeas : AEStronglyMeasurable f (Pr x) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun N => (hSmeas N).aestronglyMeasurable) hlim
  have hfbound : ∀ᵐ w ∂(Pr x), |f w| ≤ B := by
    filter_upwards [hgood, hlim] with w hw hl
    exact le_of_tendsto' hl.abs (fun N => hSbound N w hw.2)
  have hfint : Integrable f (Pr x) :=
    Integrable.of_bound hfmeas B (by filter_upwards [hfbound] with w hw; rwa [Real.norm_eq_abs])
  have hDCT : Tendsto (fun N => ∫ w, S N w ∂(Pr x)) atTop (𝓝 (∫ w, f w ∂(Pr x))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun N => (hSmeas N).aestronglyMeasurable) (integrable_const B) (fun N => ?_) hlim
    filter_upwards [hgood] with w hw
    rw [Real.norm_eq_abs]; exact hSbound N w hw.2
  have hFint : ∀ k, Integrable (FT H t A τ k) (Pr x) := by
    intro k
    refine Integrable.of_bound (FT_meas t A hτ k).aestronglyMeasurable (H.beta ^ k * K) ?_
    filter_upwards [hgood] with w hw
    rw [Real.norm_eq_abs]; exact FT_bound t A τ k w hw.2
  have hbint : ∀ k, Integrable (bT H t τ k) (Pr x) := by
    intro k
    refine Integrable.of_bound ?_ (H.beta ^ k * (2 * |t| + H.M)) ?_
    · have hi := ind_meas hτ k
      exact (by unfold bT; fun_prop : Measurable (bT H t τ k)).aestronglyMeasurable
    · filter_upwards [hgood] with w hw
      rw [Real.norm_eq_abs]
      unfold bT
      rw [abs_mul, abs_mul, abs_of_nonneg (ind_nonneg τ k w),
        abs_of_nonneg (pow_nonneg hb0.le k)]
      have hv0 := v_bound t _ (hw.2 k)
      have : |t - max (w k) t| ≤ 2 * |t| + H.M := by
        calc _ ≤ |t| + |max (w k) t| := abs_sub _ _
          _ ≤ _ := by linarith
      calc ind τ k w * (H.beta ^ k * |t - max (w k) t|)
          ≤ 1 * (H.beta ^ k * (2 * |t| + H.M)) := by
            apply mul_le_mul (ind_le_one τ k w) _ (by positivity) zero_le_one
            exact mul_le_mul le_rfl this (abs_nonneg _) (pow_nonneg hb0.le k)
        _ = _ := one_mul _
  have haint : ∀ k, Integrable (aT H t A τ k) (Pr x) := by
    intro k
    have : aT H t A τ k = fun w => FT H t A τ k w - bT H t τ k w := by
      funext w; unfold FT; ring
    rw [this]; exact (hFint k).sub (hbint k)
  have hSint : ∀ N, ∫ w, S N w ∂(Pr x)
      = max x t + ∑ k ∈ Finset.range N, ∫ w, bT H t τ k w ∂(Pr x) := by
    intro N
    simp only [S]
    rw [integral_add (integrable_const _) (integrable_finset_sum _ (fun k _ => hFint k)),
      integral_const, integral_finset_sum _ (fun k _ => hFint k)]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold FT
    rw [integral_add (haint k) (hbint k), aT_int hPr x t A hA hτ k, zero_add]
  have hSle : ∀ N, ∫ w, S N w ∂(Pr x) ≤ max x t := by
    intro N
    rw [hSint N]
    have : ∑ k ∈ Finset.range N, ∫ w, bT H t τ k w ∂(Pr x) ≤ 0 :=
      Finset.sum_nonpos (fun k _ => integral_nonpos (fun w => bT_nonpos t τ k w))
    linarith
  have hreward_le : ∀ᵐ w ∂(Pr x), H.toProblem.reward τ w ≤ f w := by
    filter_upwards [hgood, hfin'] with w hw hne
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
    have hn' : τ w = (n : ℕ∞) := hn.symm
    simp only [f]
    rw [tele x t A ht τ w n hn' hw.1, reward_coe H τ w n hn']
    have : w n ≤ max (w n) t := le_max_left _ _
    have := pow_nonneg hb0.le n
    nlinarith
  refine ⟨?_, f, hfint, ?_, hreward_le, le_of_tendsto' hDCT hSle, ?_⟩
  · -- integrability of the reward
    refine Integrable.of_bound (reward_meas H hτ).aestronglyMeasurable
      (H.c * (1 - H.beta)⁻¹ + H.M) ?_
    filter_upwards [hgood, hfin'] with w hw hne
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [reward_coe H τ w n hn.symm, Real.norm_eq_abs]
    have hc := H.c_pos
    have hwn := hw.2 n
    have hm := H.m_pos
    calc |(∑ k ∈ Finset.range n, H.beta ^ k * (-H.c)) + H.beta ^ n * w n|
        ≤ |∑ k ∈ Finset.range n, H.beta ^ k * (-H.c)| + |H.beta ^ n * w n| := abs_add_le _ _
      _ ≤ H.c * (1 - H.beta)⁻¹ + H.M := by
          gcongr
          · rw [← Finset.sum_mul, abs_mul, abs_neg, abs_of_pos hc,
              abs_of_nonneg (Finset.sum_nonneg (fun k _ => pow_nonneg hb0.le k)), mul_comm]
            gcongr
            exact geom_le n
          · rw [abs_mul, abs_of_nonneg (pow_nonneg hb0.le n), abs_of_pos (by linarith [hwn.1])]
            calc H.beta ^ n * w n ≤ 1 * w n := by
                  gcongr
                  · linarith [hwn.1]
                  · exact pow_le_one₀ hb0.le hb1.le
              _ ≤ H.M := by linarith [hwn.2]
  · filter_upwards [hgood] with w hw n hn
    exact tele x t A ht τ w n hn hw.1
  · intro hb
    have : ∀ N, ∫ w, S N w ∂(Pr x) = max x t := by
      intro N
      rw [hSint N]
      have : ∀ k ∈ Finset.range N, ∫ w, bT H t τ k w ∂(Pr x) = 0 := by
        intro k _
        rw [integral_eq_zero_of_ae (hb k)]
      rw [Finset.sum_eq_zero this, add_zero]
    refine tendsto_nhds_unique hDCT ?_
    simp only [this]
    exact tendsto_const_nhds

end HSAux

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace HSAux
open MDPFinance.OptimalStopping

variable {H : HouseSelling}

lemma ereal_int {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    erealIntegral μ (fun w => ((f w : ℝ) : EReal)) = ((∫ w, f w ∂μ : ℝ) : EReal) := by
  unfold erealIntegral
  have e1 : ∀ w, (((f w : ℝ) : EReal) ⊔ 0).toENNReal = ENNReal.ofReal (f w) := by
    intro w
    rcases le_total (f w) 0 with h | h
    · rw [max_eq_right (by exact_mod_cast h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left (by exact_mod_cast h), EReal.real_coe_toENNReal]
  have e2 : ∀ w, ((-((f w : ℝ) : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-f w) := by
    intro w
    rw [← EReal.coe_neg]
    rcases le_total (-f w) 0 with h | h
    · rw [max_eq_right (by exact_mod_cast h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left (by exact_mod_cast h), EReal.real_coe_toENNReal]
  simp only [e1, e2]
  have h2 : (∫⁻ a, ENNReal.ofReal (-f a) ∂μ) ≠ ⊤ := by simpa using hf.neg.lintegral_lt_top.ne
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, EReal.coe_sub,
    EReal.coe_ennreal_toReal hf.lintegral_lt_top.ne,
    EReal.coe_ennreal_toReal h2, sub_eq_add_neg]

lemma Q_Iio (y : ℝ) : H.Q (Set.Ico H.m y) = H.Q (Set.Iio y) := by
  have h0 : H.Q (Set.Iio H.m) = 0 := by
    refine le_antisymm (le_trans (measure_mono ?_) H.Q_supp.le) zero_le
    intro z hz; exact Or.inl hz
  refine le_antisymm (measure_mono (fun z hz => hz.2)) ?_
  calc H.Q (Set.Iio y) ≤ H.Q (Set.Ico H.m y ∪ Set.Iio H.m) := measure_mono (by
        intro z hz
        by_cases h : H.m ≤ z
        · exact Or.inl ⟨h, hz⟩
        · exact Or.inr (lt_of_not_ge h))
    _ ≤ H.Q (Set.Ico H.m y) + H.Q (Set.Iio H.m) := measure_union_le _ _
    _ = _ := by rw [h0, add_zero]

lemma int_cont : Continuous (fun t => ∫ y, max y t ∂H.Q) := by
  haveI := H.Q_prob
  refine (LipschitzWith.of_dist_le_mul (K := 1) (fun t s => ?_)).continuous
  rw [Real.dist_eq, ← integral_sub (v_int t) (v_int s)]
  have := norm_integral_le_of_norm_le_const (μ := H.Q) (f := fun y => max y t - max y s)
    (C := |t - s|) (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs]
      have := abs_max_sub_max_le_max y t y s
      simpa using this))
  simp only [probReal_univ, mul_one, Real.norm_eq_abs] at this
  simpa [Real.dist_eq] using this

lemma int_low (t : ℝ) (ht : t ≤ H.m) : ∫ y, max y t ∂H.Q = ∫ y, y ∂H.Q := by
  refine integral_congr_ae ?_
  filter_upwards [Q_ae] with y hy
  exact max_eq_left (ht.trans hy.1)

lemma int_high (t : ℝ) (ht : H.M ≤ t) : ∫ y, max y t ∂H.Q = t := by
  haveI := H.Q_prob
  rw [integral_congr_ae (g := fun _ => t)]
  · simp
  filter_upwards [Q_ae] with y hy
  exact max_eq_right (hy.2.trans ht)

lemma mean_ge : H.m ≤ ∫ y, y ∂H.Q := by
  haveI := H.Q_prob
  have : ∫ _y, H.m ∂H.Q ≤ ∫ y, y ∂H.Q := by
    refine integral_mono_ae (integrable_const _) ?_ ?_
    · simpa using (v_int (H := H) H.m).congr (by
        filter_upwards [Q_ae] with y hy; exact max_eq_left hy.1)
    · filter_upwards [Q_ae] with y hy; exact hy.1
  simpa using this

/-- the fixed point `t* = -c + β ∫ max(y, t*) dQ` -/
lemma fixed : ∃ t : ℝ, t < H.M ∧ -H.c + H.beta * ∫ y, max y t ∂H.Q = t := by
  let g : ℝ → ℝ := fun t => -H.c + H.beta * (∫ y, max y t ∂H.Q) - t
  have hg : Continuous g := by
    have := int_cont (H := H); fun_prop
  set a := min H.m (-H.c + H.beta * H.m) with ha
  have hab : a ≤ H.M := (min_le_left _ _).trans H.m_lt_M.le
  have hga : 0 ≤ g a := by
    simp only [g]
    rw [int_low a (min_le_left _ _)]
    have h1 := mean_ge (H := H)
    have h2 : a ≤ -H.c + H.beta * H.m := min_le_right _ _
    have := beta_pos (H := H)
    nlinarith
  have hgM : g H.M < 0 := by
    simp only [g]
    rw [int_high H.M le_rfl]
    have := H.c_pos; have := beta_lt (H := H); have := H.m_pos; have := H.m_lt_M
    nlinarith
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' hab hg.continuousOn ⟨hgM.le, hga⟩
  refine ⟨t, lt_of_le_of_ne ht.2 ?_, by simp only [g] at hgt; linarith⟩
  rintro rfl
  exact absurd hgt (ne_of_lt hgM)

lemma split_ineq (t y : ℝ) :
    ∫ z in Set.Ici y, z ∂H.Q + (H.Q (Set.Iio y)).toReal * t ≤ ∫ z, max z t ∂H.Q := by
  haveI := H.Q_prob
  have hid : Integrable (fun z : ℝ => z) H.Q :=
    (v_int (H := H) H.m).congr (by filter_upwards [Q_ae] with y hy; exact max_eq_left hy.1)
  rw [← integral_add_compl (measurableSet_Ici (a := y)) (v_int t), Set.compl_Ici]
  apply add_le_add
  · exact setIntegral_mono hid.integrableOn (v_int t).integrableOn (fun z => le_max_left z t)
  · have : ∫ _z in Set.Iio y, t ∂H.Q = (H.Q (Set.Iio y)).toReal * t := by
      simp [Measure.real]
    rw [← this]
    exact setIntegral_mono (integrable_const t) (v_int t).integrableOn (fun z => le_max_right z t)

lemma split_eq (t y : ℝ) (hty : t ≤ y) (hlow : ∀ᵐ z ∂H.Q, z < y → z ≤ t) :
    ∫ z in Set.Ici y, z ∂H.Q + (H.Q (Set.Iio y)).toReal * t = ∫ z, max z t ∂H.Q := by
  haveI := H.Q_prob
  rw [← integral_add_compl (measurableSet_Ici (a := y)) (v_int t), Set.compl_Ici]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
    exact (max_eq_left (hty.trans hz)).symm
  · have : ∫ _z in Set.Iio y, t ∂H.Q = (H.Q (Set.Iio y)).toReal * t := by
      simp [Measure.real]
    rw [← this]
    refine setIntegral_congr_ae measurableSet_Iio ?_
    filter_upwards [hlow] with z hz hzy
    exact (max_eq_right (hz hzy)).symm

end HSAux

open MeasureTheory ProbabilityTheory Filter Topology MDPFinance.OptimalStopping HSAux in
theorem solution (H : HouseSelling) (Pr : ℝ → Measure (ℕ → ℝ))
    (hPr : H.toProblem.IsPathLaw Pr) :
    ∃ xstar ∈ H.E,
      IsGreatest (H.thresholdObjective '' H.E) (H.thresholdObjective xstar) ∧
      xstar < H.M ∧
      IsStopTime (hitTime {y : ℝ | xstar ≤ y}) ∧
      (∀ x ∈ H.E, Pr x {w | hitTime {y : ℝ | xstar ≤ y} w = ⊤} = 0) ∧
      ∀ x ∈ H.E, H.toProblem.EReward Pr (hitTime {y : ℝ | xstar ≤ y}) x =
        H.toProblem.Vstar Pr x := by
  haveI := H.Q_prob
  obtain ⟨t, htM, ht⟩ := fixed (H := H)
  set A := ∫ y, max y t ∂H.Q with hA
  have hb0 := beta_pos (H := H)
  have hb1 := beta_lt (H := H)
  have hc := H.c_pos
  have hm := H.m_pos
  have hmM := H.m_lt_M
  set xs := max t H.m with hxs
  have hxsE : xs ∈ H.E := ⟨le_max_right _ _, max_le htM.le hmM.le⟩
  have htxs : t ≤ xs := le_max_left _ _
  have hlow : ∀ z ∈ Set.Icc H.m H.M, z < xs → z ≤ t := by
    intro z hz hzx
    rcases le_total H.m t with h | h
    · rw [hxs, max_eq_left h] at hzx; exact hzx.le
    · rw [hxs, max_eq_right h] at hzx; exact absurd hz.1 (not_le.2 hzx)
  have hlowQ : ∀ᵐ z ∂H.Q, z < xs → z ≤ t := by
    filter_upwards [Q_ae] with z hz using hlow z hz
  have hS : {y : ℝ | xs ≤ y} = Set.Ici xs := rfl
  have hSmeas : MeasurableSet {y : ℝ | xs ≤ y} := measurableSet_Ici
  -- positivity of `Q [xs, ∞)`
  have hpos : H.Q (Set.Iio xs) < 1 := by
    by_contra hcon
    have h1 : H.Q (Set.Iio xs) = 1 := le_antisymm prob_le_one (not_lt.1 hcon)
    have h2 : H.Q (Set.Ici xs) = 0 := by
      have := prob_compl_eq_one_sub (μ := H.Q) (measurableSet_Iio (a := xs))
      rw [Set.compl_Iio, h1, tsub_self] at this; exact this
    have hae : ∀ᵐ z ∂H.Q, z < xs := by
      have hset : {a : ℝ | ¬ a < xs} = Set.Ici xs := by ext; simp
      rw [ae_iff, hset]; exact h2
    have hAt : A = t := by
      rw [hA, integral_congr_ae (g := fun _ => t)]
      · simp
      filter_upwards [hae, hlowQ] with z hz hz2 using max_eq_right (hz2 hz)
    rcases le_total H.m t with h | h
    · rw [hAt] at ht; nlinarith
    · -- xs = m, but z ≥ m a.s.
      have : ∀ᵐ z ∂H.Q, False := by
        filter_upwards [hae, Q_ae] with z hz hz2
        rw [hxs, max_eq_right h] at hz; linarith [hz2.1]
      have h3 := ae_iff.1 this
      simp only [not_false_eq_true, Set.setOf_true] at h3
      rw [measure_univ] at h3
      exact one_ne_zero h3
  refine ⟨xs, hxsE, ⟨⟨xs, hxsE, rfl⟩, ?_⟩, max_lt htM hmM, hit_isStop _ hSmeas, ?_, ?_⟩
  · -- maximality of the threshold objective
    have hden : ∀ y, 0 < 1 - H.beta * (H.Q (Set.Ico H.m y)).toReal := by
      intro y
      have : (H.Q (Set.Ico H.m y)).toReal ≤ 1 := by
        have := prob_le_one (μ := H.Q) (s := Set.Ico H.m y)
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
      have := ENNReal.toReal_nonneg (a := H.Q (Set.Ico H.m y))
      nlinarith
    have hval : H.thresholdObjective xs = A := by
      unfold HouseSelling.thresholdObjective
      rw [div_eq_iff (hden xs).ne', Q_Iio]
      have := split_eq (H := H) t xs htxs hlowQ
      rw [← hA] at this
      have hcA : -H.c = t - H.beta * A := by linarith
      rw [neg_mul, ← neg_mul, hcA]
      linarith
    rintro _ ⟨y, _, rfl⟩
    rw [hval]
    unfold HouseSelling.thresholdObjective
    rw [div_le_iff₀ (hden y), Q_Iio]
    have := split_ineq (H := H) t y
    rw [← hA] at this
    have hcA : -H.c = t - H.beta * A := by linarith
    rw [neg_mul, ← neg_mul, hcA]
    nlinarith [ENNReal.toReal_nonneg (a := H.Q (Set.Iio y))]
  · -- a.s. finiteness
    intro x hx
    have hbound : ∀ N : ℕ, Pr x {w | hitTime {y : ℝ | xs ≤ y} w = ⊤}
        ≤ H.Q (Set.Iio xs) ^ N := by
      intro N
      have hbox := box hPr x N (fun i => if i = 0 then Set.univ else Set.Iio xs)
        (fun i => by split_ifs <;> simp [measurableSet_Iio])
      simp only [Set.indicator, if_true, Set.mem_univ, Nat.add_one_ne_zero, if_false,
        Finset.prod_const, Finset.card_range] at hbox
      rw [← hbox]
      refine measure_mono (fun w hw => ?_)
      simp only [Set.mem_setOf_eq] at hw ⊢
      intro i _
      split_ifs
      · trivial
      · by_contra hcon
        have : hitTime {y : ℝ | xs ≤ y} w ≤ (i : ℕ∞) :=
          (hit_le_iff _ w i).2 ⟨i, le_rfl, (show xs ≤ w i from not_lt.1 (by simpa using hcon))⟩
        rw [hw] at this; exact absurd this (by simp)
    have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hpos
    exact le_antisymm (ge_of_tendsto' hlim (fun N => hbound N)) zero_le
  · -- optimality
    intro x hx
    have hfin : ∀ τ : (ℕ → ℝ) → ℕ∞, IsStopTime τ → Pr x {w | τ w = ⊤} = 0 →
        H.toProblem.EReward Pr τ x ≤ ((max x t : ℝ) : EReal) := by
      intro τ hτ hτfin
      obtain ⟨hRint, f, hfint, _, hRf, hfle, _⟩ := core hPr x hx t A hA ht hτ hτfin
      unfold StationaryProblem.EReward
      rw [ereal_int hRint]
      exact_mod_cast (integral_mono_ae hRint hfint hRf).trans hfle
    have hstar : H.toProblem.EReward Pr (hitTime {y : ℝ | xs ≤ y}) x = ((max x t : ℝ) : EReal) := by
      have hτ := hit_isStop _ hSmeas
      have hτfin : Pr x {w | hitTime {y : ℝ | xs ≤ y} w = ⊤} = 0 := by
        have hbound : ∀ N : ℕ, Pr x {w | hitTime {y : ℝ | xs ≤ y} w = ⊤}
            ≤ H.Q (Set.Iio xs) ^ N := by
          intro N
          have hbox := box hPr x N (fun i => if i = 0 then Set.univ else Set.Iio xs)
            (fun i => by split_ifs <;> simp [measurableSet_Iio])
          simp only [Set.indicator, if_true, Set.mem_univ, Nat.add_one_ne_zero, if_false,
            Finset.prod_const, Finset.card_range] at hbox
          rw [← hbox]
          refine measure_mono (fun w hw => ?_)
          simp only [Set.mem_setOf_eq] at hw ⊢
          intro i _
          split_ifs
          · trivial
          · by_contra hcon
            have : hitTime {y : ℝ | xs ≤ y} w ≤ (i : ℕ∞) :=
              (hit_le_iff _ w i).2 ⟨i, le_rfl, (show xs ≤ w i from not_lt.1 (by simpa using hcon))⟩
            rw [hw] at this; exact absurd this (by simp)
        have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hpos
        exact le_antisymm (ge_of_tendsto' hlim (fun N => hbound N)) zero_le
      obtain ⟨hRint, f, hfint, hfform, _, _, hfeq⟩ := core hPr x hx t A hA ht hτ hτfin
      have hgood := ae_good hPr x hx
      have hne : ∀ᵐ w ∂(Pr x), hitTime {y : ℝ | xs ≤ y} w ≠ ⊤ := by
        rw [ae_iff]; simpa using hτfin
      have hb : ∀ k, ∀ᵐ w ∂(Pr x), bT H t (hitTime {y : ℝ | xs ≤ y}) k w = 0 := by
        intro k
        filter_upwards [hgood, hne] with w hw hn
        obtain ⟨n, hn'⟩ := WithTop.ne_top_iff_exists.1 hn
        unfold bT
        by_cases hk : k < n
        · have := (hit_coe _ w n hn'.symm).2 k hk
          simp only [Set.mem_setOf_eq, not_le] at this
          rw [max_eq_right (hlow _ (hw.2 k) this)]
          ring
        · rw [ind_of_ge _ k w n hn'.symm (not_lt.1 hk)]; ring
      have hRf : ∀ᵐ w ∂(Pr x), H.toProblem.reward (hitTime {y : ℝ | xs ≤ y}) w = f w := by
        filter_upwards [hfform, hne] with w hw hn
        obtain ⟨n, hn'⟩ := WithTop.ne_top_iff_exists.1 hn
        rw [hw n hn'.symm, reward_coe H _ w n hn'.symm]
        have := (hit_coe _ w n hn'.symm).1
        simp only [Set.mem_setOf_eq] at this
        rw [max_eq_left (htxs.trans this)]
      unfold StationaryProblem.EReward
      rw [ereal_int hRint, integral_congr_ae hRf, hfeq hb]
    rw [hstar]
    refine le_antisymm ?_ ?_
    · unfold StationaryProblem.Vstar
      refine le_iSup₂_of_le (hitTime {y : ℝ | xs ≤ y}) ⟨hit_isStop _ hSmeas, ?_⟩ hstar.ge
      have hbound : ∀ N : ℕ, Pr x {w | hitTime {y : ℝ | xs ≤ y} w = ⊤}
          ≤ H.Q (Set.Iio xs) ^ N := by
        intro N
        have hbox := box hPr x N (fun i => if i = 0 then Set.univ else Set.Iio xs)
          (fun i => by split_ifs <;> simp [measurableSet_Iio])
        simp only [Set.indicator, if_true, Set.mem_univ, Nat.add_one_ne_zero, if_false,
          Finset.prod_const, Finset.card_range] at hbox
        rw [← hbox]
        refine measure_mono (fun w hw => ?_)
        simp only [Set.mem_setOf_eq] at hw ⊢
        intro i _
        split_ifs
        · trivial
        · by_contra hcon
          have : hitTime {y : ℝ | xs ≤ y} w ≤ (i : ℕ∞) :=
            (hit_le_iff _ w i).2 ⟨i, le_rfl, (show xs ≤ w i from not_lt.1 (by simpa using hcon))⟩
          rw [hw] at this; exact absurd this (by simp)
      have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hpos
      exact le_antisymm (ge_of_tendsto' hlim (fun N => hbound N)) zero_le
    · unfold StationaryProblem.Vstar
      exact iSup₂_le (fun τ h => hfin τ h.1 h.2)
