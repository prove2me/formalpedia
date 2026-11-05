-- Prove2me | solution 1 for LimitedPriceChanges.AlgorithmI.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:06:44.85322+00:00
-- url     : https://prove2.me/submissions/64ada8b7-f153-4d1a-87dc-e92655490280
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm
import Theorems.Thm_LimitedPriceChanges_AlgorithmI_eq_25
import Theorems.Thm_LimitedPriceChanges_AlgorithmI_eq_26
import Theorems.Thm_LimitedPriceChanges_AlgorithmI_stage_carryover

namespace LPCThm1Aux

/-- The law of an adapted price process has total mass one. -/
theorem mass_eq_one (f : ℕ → ℝ → ℝ) (Pset : Set ℝ) (hf0 : ∀ p ∈ Pset, ∀ d, 0 ≤ f d p)
    (hf1 : ∀ p ∈ Pset, HasSum (fun d => f d p) 1) :
    ∀ (T : ℕ) (price : Fin T → (Fin T → ℕ) → ℝ), (∀ s d, price s d ∈ Pset) →
      (∀ s d d', (∀ t : Fin T, t < s → d t = d' t) → price s d = price s d') →
      ∑' d : Fin T → ℕ, ∏ s, ENNReal.ofReal (f (d s) (price s d)) = 1 := by
  intro T
  induction T with
  | zero =>
    intro price _ _
    rw [tsum_eq_single (fun i => i.elim0)]
    · simp
    · intro d hd
      exact absurd (funext (fun i => i.elim0)) hd
  | succ T ih =>
    intro price hP hadapt
    let price' : Fin T → (Fin T → ℕ) → ℝ := fun s g => price (Fin.castSucc s) (Fin.snoc g 0)
    let q : (Fin T → ℕ) → ℝ := fun g => price (Fin.last T) (Fin.snoc g 0)
    have hsnoc : ∀ (g : Fin T → ℕ) (a : ℕ),
        ∏ s : Fin (T + 1), ENNReal.ofReal (f ((Fin.snoc g a : Fin (T + 1) → ℕ) s)
          (price s (Fin.snoc g a))) =
        (∏ s : Fin T, ENNReal.ofReal (f (g s) (price' s g))) * ENNReal.ofReal (f a (q g)) := by
      intro g a
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro s _
        simp only [Fin.snoc_castSucc, price']
        congr 2
        apply hadapt
        intro t ht
        have : (t : ℕ) < T := by
          have := s.isLt
          have h2 : (t : ℕ) < (s : ℕ) := by simpa [Fin.lt_def] using ht
          omega
        have ht' : t = Fin.castSucc ⟨t, this⟩ := by ext; simp
        rw [ht', Fin.snoc_castSucc, Fin.snoc_castSucc]
      · simp only [Fin.snoc_last, q]
        congr 2
        apply hadapt
        intro t ht
        have : (t : ℕ) < T := by simpa [Fin.lt_def] using ht
        have ht' : t = Fin.castSucc ⟨t, this⟩ := by ext; simp
        rw [ht', Fin.snoc_castSucc, Fin.snoc_castSucc]
    rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => ℕ)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
    have hrw : ∀ (g : Fin T → ℕ) (a : ℕ),
        (∏ s : Fin (T + 1), ENNReal.ofReal (f ((Fin.snocEquiv (fun _ : Fin (T + 1) => ℕ) (a, g)) s)
          (price s (Fin.snocEquiv (fun _ : Fin (T + 1) => ℕ) (a, g))))) =
        (∏ s : Fin T, ENNReal.ofReal (f (g s) (price' s g))) * ENNReal.ofReal (f a (q g)) :=
      fun g a => hsnoc g a
    simp_rw [hrw, ENNReal.tsum_mul_left]
    have hone : ∀ g : Fin T → ℕ, ∑' a : ℕ, ENNReal.ofReal (f a (q g)) = 1 := by
      intro g
      have hq : q g ∈ Pset := hP _ _
      rw [← ENNReal.ofReal_tsum_of_nonneg (hf0 _ hq) (hf1 _ hq).summable, (hf1 _ hq).tsum_eq,
        ENNReal.ofReal_one]
    simp_rw [hone, mul_one]
    apply ih price' (fun s g => hP _ _)
    intro s g g' hgg
    simp only [price']
    apply hadapt
    intro t ht
    by_cases htT : (t : ℕ) < T
    · have ht' : t = Fin.castSucc ⟨t, htT⟩ := by ext; simp
      rw [ht', Fin.snoc_castSucc, Fin.snoc_castSucc]
      apply hgg
      simpa [Fin.lt_def] using ht
    · exfalso
      have := s.isLt
      simp [Fin.lt_def] at ht
      omega


open LimitedPriceChanges.AlgorithmI

theorem runStage_congr (d d' : ℕ → ℕ) (ytil : ℕ) : ∀ n s0 x,
    (∀ t, s0 ≤ t → t < s0 + n → d t = d' t) →
    Alg.runStage d ytil s0 n x = Alg.runStage d' ytil s0 n x := by
  intro n
  induction n with
  | zero => intro s0 x _; simp [Alg.runStage]
  | succ n ih =>
    intro s0 x h
    simp only [Alg.runStage]
    have h0 : d s0 = d' s0 := h s0 le_rfl (by omega)
    rw [h0, ih (s0 + 1) _ (fun t ht1 ht2 => h t (by omega) (by omega))]

theorem runStage_le (d : ℕ → ℕ) (ytil B : ℕ) (hy : ytil ≤ B) : ∀ n s0 x, x ≤ B →
    (Alg.runStage d ytil s0 n x).2 ≤ B := by
  intro n
  induction n with
  | zero => intro s0 x hx; simpa [Alg.runStage] using hx
  | succ n ih =>
    intro s0 x hx
    simp only [Alg.runStage]
    apply ih
    have : max x ytil ≤ B := max_le hx hy
    omega

variable {S : Model} (A : Alg S)

theorem stageStart_mono (T : ℕ) {a b : ℕ} (hab : a ≤ b) : A.stageStart T a ≤ A.stageStart T b := by
  unfold Alg.stageStart
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hab)

theorem stageStart_succ (T i : ℕ) (hi : 1 ≤ i) :
    A.stageStart T (i + 1) = A.stageStart T i + A.stageLen T i := by
  unfold Alg.stageStart
  rw [Finset.sum_Ico_succ_top hi]

theorem stageState_congr (T : ℕ) : ∀ k (d d' : ℕ → ℕ),
    (∀ t, t < A.stageStart T (k + 1) → d t = d' t) →
    A.stageState T d k = A.stageState T d' k := by
  intro k
  induction k with
  | zero => intro d d' _; simp [Alg.stageState]
  | succ k ih =>
    intro d d' h
    have hk := ih d d' (fun t ht => h t (lt_of_lt_of_le ht (stageStart_mono A T (by omega))))
    simp only [Alg.stageState]
    rw [hk]
    have hsucc := stageStart_succ A T (k + 1) (by omega)
    rw [runStage_congr d d' _ (A.stageLen T (k + 1)) (A.stageStart T (k + 1)) _
      (fun t _ ht2 => h t (by omega))]

theorem stageOf_le (T s : ℕ) : A.stageOf T s ≤ A.m + 1 := by
  unfold Alg.stageOf
  have := Finset.card_filter_le (Finset.Icc 1 A.m) (fun j => A.stageStart T (j + 1) ≤ s)
  simp at this
  omega

theorem one_le_stageOf (T s : ℕ) : 1 ≤ A.stageOf T s := by
  unfold Alg.stageOf; omega

theorem stageStart_stageOf_le (T s : ℕ) : A.stageStart T (A.stageOf T s) ≤ s := by
  set i := A.stageOf T s with hi
  by_cases hi1 : i = 1
  · rw [hi1]; simp [Alg.stageStart]
  have hi2 : 2 ≤ i := by have := one_le_stageOf A T s; omega
  set F := (Finset.Icc 1 A.m).filter (fun j => A.stageStart T (j + 1) ≤ s) with hF
  have hcard : F.card = i - 1 := by
    rw [hi]; unfold Alg.stageOf; rw [← hF]; omega
  by_contra hlt
  push Not at hlt
  have hsub : F ⊆ Finset.Icc 1 (i - 2) := by
    intro j hj
    rw [hF, Finset.mem_filter, Finset.mem_Icc] at hj
    rw [Finset.mem_Icc]
    refine ⟨hj.1.1, ?_⟩
    by_contra hji
    have : A.stageStart T i ≤ A.stageStart T (j + 1) := stageStart_mono A T (by omega)
    omega
  have := Finset.card_le_card hsub
  simp at this
  omega

theorem price_adapted (T : ℕ) (s : Fin T) (d d' : Fin T → ℕ)
    (h : ∀ t : Fin T, t < s → d t = d' t) : A.price T s d = A.price T s d' := by
  unfold Alg.price Alg.phat
  congr 1
  apply stageState_congr
  intro t ht
  have h1 : A.stageOf T s - 1 + 1 = A.stageOf T s := by
    have := one_le_stageOf A T s; omega
  rw [h1] at ht
  have hts : t < s := lt_of_lt_of_le ht (stageStart_stageOf_le A T s)
  have htT : t < T := lt_trans hts s.isLt
  simp only [Alg.extend, dif_pos htT]
  exact h ⟨t, htT⟩ (by simpa [Fin.lt_def] using hts)

theorem ytildeOf_mem (y : ℕ) (hy : y ∈ S.Y) : A.ytildeOf y ∈ S.Y := by
  unfold Alg.ytildeOf
  simp only [Model.Y, Finset.mem_Icc] at hy ⊢
  split_ifs
  · exact hy
  · constructor
    · exact le_min (le_max_right _ _) S.yl_le_yh
    · exact min_le_right _ _

theorem stageState_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T : ℕ)
    (d : ℕ → ℕ) : ∀ k, (A.stageState T d k).1 ∈ S.P ∧ (A.stageState T d k).2.1 ∈ S.Y ∧
      (A.stageState T d k).2.2 ≤ S.yh := by
  intro k
  induction k with
  | zero => exact ⟨hA.p1_mem, hA.y1_mem, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨hp, hy, hx⟩ := ih
    simp only [Alg.stageState]
    set r := Alg.runStage d (A.ytildeOf (A.stageState T d k).2.1) (A.stageStart T (k + 1))
      (A.stageLen T (k + 1)) (A.stageState T d k).2.2
    have hz : A.mle (A.stageState T d k).1 r.1 ∈ S.Z := (hA.mle _ hp r.1).1
    have hyk : A.yplug (A.mle (A.stageState T d k).1 r.1) ∈ S.Y := (hA.plugIn _ hz).1
    refine ⟨(hS.priceSelection _ hyk _ hz).1, hyk, ?_⟩
    have hyt := ytildeOf_mem A _ hy
    simp only [Model.Y, Finset.mem_Icc] at hyt
    exact runStage_le d _ S.yh hyt.2 _ _ _ hx

theorem price_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T : ℕ) (s : Fin T)
    (d : Fin T → ℕ) : A.price T s d ∈ S.P :=
  (stageState_mem A z hS hA T _ _).1

theorem phat_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T i : ℕ)
    (d : Fin T → ℕ) : A.phat T i d ∈ S.P :=
  (stageState_mem A z hS hA T _ _).1

theorem yhat_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T i : ℕ)
    (d : Fin T → ℕ) : A.yhat T i d ∈ S.Y :=
  (stageState_mem A z hS hA T _ _).2.1

theorem level_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T : ℕ) (s : Fin T)
    (d : Fin T → ℕ) : A.level T s d ∈ S.Y := by
  unfold Alg.level
  have hyt := ytildeOf_mem A _ (yhat_mem A z hS hA T (A.stageOf T s) d)
  have hx := (stageState_mem A z hS hA T (Alg.extend d) (A.stageOf T s - 1)).2.2
  simp only [Model.Y, Finset.mem_Icc] at hyt ⊢
  have hr := runStage_le (Alg.extend d) (A.ytilde T (A.stageOf T s) d) S.yh hyt.2
    ((s : ℕ) - A.stageStart T (A.stageOf T s)) (A.stageStart T (A.stageOf T s)) _ hx
  exact ⟨le_trans hyt.1 (le_max_right _ _), max_le hr hyt.2⟩

theorem mass_one (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T : ℕ) :
    ∑' d : Fin T → ℕ, A.pathWeight z T d = 1 := by
  unfold Alg.pathWeight
  exact mass_eq_one (fun d p => S.f d p z) S.P
    (fun p hp d => S.f_nonneg p hp z hS.z_mem d) (fun p hp => S.f_hasSum p hp z hS.z_mem)
    T (fun s d => A.price T s d) (fun s d => price_mem A z hS hA T s d)
    (fun s d d' h => price_adapted A T s d d' h)

end LPCThm1Aux

namespace LPC25Aux

open LimitedPriceChanges.AlgorithmI

variable {S : Model} (A : Alg S)

theorem stageStart_mono (T : ℕ) {a b : ℕ} (hab : a ≤ b) : A.stageStart T a ≤ A.stageStart T b := by
  unfold Alg.stageStart
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hab)

theorem stageStart_succ (T i : ℕ) (hi : 1 ≤ i) :
    A.stageStart T (i + 1) = A.stageStart T i + A.stageLen T i := by
  unfold Alg.stageStart
  rw [Finset.sum_Ico_succ_top hi]

theorem stageOf_le (T s : ℕ) : A.stageOf T s ≤ A.m + 1 := by
  unfold Alg.stageOf
  have := Finset.card_filter_le (Finset.Icc 1 A.m) (fun j => A.stageStart T (j + 1) ≤ s)
  simp at this
  omega

theorem one_le_stageOf (T s : ℕ) : 1 ≤ A.stageOf T s := by
  unfold Alg.stageOf; omega

/-- A period of stage `i ≥ 2` lies in `[tᵢ, tᵢ + Iᵢ)`, provided `t_{m+1} ≤ T` and `s < T`. -/
theorem mem_stage (T s i : ℕ) (hs : s < T) (hT : A.stageStart T (A.m + 1) ≤ T)
    (hi2 : 2 ≤ i) (hsi : A.stageOf T s = i) :
    A.stageStart T i ≤ s ∧ s < A.stageStart T i + A.stageLen T i := by
  have him : i ≤ A.m + 1 := hsi ▸ stageOf_le A T s
  set F := (Finset.Icc 1 A.m).filter (fun j => A.stageStart T (j + 1) ≤ s) with hF
  have hcard : F.card = i - 1 := by
    unfold Alg.stageOf at hsi; rw [← hF] at hsi; omega
  constructor
  · by_contra hlt
    push Not at hlt
    have hsub : F ⊆ Finset.Icc 1 (i - 2) := by
      intro j hj
      rw [hF, Finset.mem_filter, Finset.mem_Icc] at hj
      rw [Finset.mem_Icc]
      refine ⟨hj.1.1, ?_⟩
      by_contra hji
      have : A.stageStart T i ≤ A.stageStart T (j + 1) := stageStart_mono A T (by omega)
      omega
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_cases hile : i ≤ A.m
    · rw [← stageStart_succ A T i (by omega)]
      by_contra hge
      push Not at hge
      have hsub : Finset.Icc 1 i ⊆ F := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        rw [hF, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hj.1, by omega⟩, ?_⟩
        exact (stageStart_mono A T (by omega)).trans hge
      have := Finset.card_le_card hsub
      simp at this
      omega
    · have hieq : i = A.m + 1 := by omega
      subst hieq
      have hlen : A.stageLen T (A.m + 1) = T - ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j := by
        unfold Alg.stageLen; simp
      have hstart : A.stageStart T (A.m + 1) = ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j := by
        unfold Alg.stageStart
        apply Finset.sum_congr (by ext j; simp [Finset.mem_Ico, Finset.mem_Icc])
        intro j hj
        simp [Finset.mem_Icc] at hj
        unfold Alg.stageLen
        rw [if_pos hj.2]
      rw [hlen]
      rw [hstart] at hT ⊢
      omega

/-- The number of periods of stage `i ≥ 2` is at most `Iᵢ`. -/
theorem card_stage (T i : ℕ) (hT : A.stageStart T (A.m + 1) ≤ T) (hi2 : 2 ≤ i) :
    ((Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = i)).card ≤
      A.stageLen T i := by
  have := Finset.card_le_card_of_injOn (fun s : Fin T => (s : ℕ))
    (s := (Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = i))
    (t := Finset.Ico (A.stageStart T i) (A.stageStart T i + A.stageLen T i))
    (fun s hs => by
      have hs' : A.stageOf T (s : ℕ) = i := by simpa using hs
      have := mem_stage A T s i s.isLt hT hi2 hs'
      simp only [Finset.coe_Ico, Set.mem_Ico]
      exact this)
    (fun a _ b _ h => Fin.ext h)
  simpa using this


theorem stageStart_last (T : ℕ) :
    A.stageStart T (A.m + 1) = ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j := by
  unfold Alg.stageStart
  apply Finset.sum_congr (by ext j; simp [Finset.mem_Ico, Finset.mem_Icc])
  intro j hj
  simp [Finset.mem_Icc] at hj
  unfold Alg.stageLen
  rw [if_pos hj.2]

/-- `T^{j/(m+1)} = u^j` with `u = T^{1/(m+1)}`. -/
theorem rpow_eq_pow (T : ℕ) (m j : ℕ) :
    (T : ℝ) ^ ((j : ℝ) / ((m : ℝ) + 1)) = ((T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; ring

theorem u_pow_succ (T m : ℕ) :
    ((T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ^ (m + 1) = T := by
  rw [← rpow_eq_pow]
  have : ((m + 1 : ℕ) : ℝ) / ((m : ℝ) + 1) = 1 := by push_cast; field_simp
  rw [this, Real.rpow_one]

theorem u_ge (T m : ℕ) (hT : (2 * m) ^ (m + 1) ≤ T) :
    (2 * m : ℝ) ≤ (T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  have h1 : ((2 * m : ℝ) ^ (m + 1)) ^ ((((m + 1 : ℕ) : ℝ))⁻¹) = 2 * m :=
    Real.pow_rpow_inv_natCast (by positivity) (by omega)
  have h2 : ((m + 1 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / ((m : ℝ) + 1) := by push_cast; ring
  rw [h2] at h1
  rw [← h1]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact_mod_cast hT

/-- For `u ≥ 2m`, the first `m` stages fit in the horizon. -/
theorem stages_fit (T : ℕ) (hm : 1 ≤ A.m) (hT : (2 * A.m) ^ (A.m + 1) ≤ T) :
    A.stageStart T (A.m + 1) ≤ T := by
  rw [stageStart_last]
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hu2 : (2 * A.m : ℝ) ≤ u := u_ge T A.m hT
  have hm1 : (1 : ℝ) ≤ A.m := by exact_mod_cast hm
  have hu1 : 1 ≤ u := by linarith
  have hsum : (∑ j ∈ Finset.Icc 1 A.m, (A.ceilLen T j : ℝ)) ≤ A.m * (u ^ A.m + 1) := by
    have : ∀ j ∈ Finset.Icc 1 A.m, (A.ceilLen T j : ℝ) ≤ u ^ A.m + 1 := by
      intro j hj
      have hj := Finset.mem_Icc.mp hj
      unfold Alg.ceilLen
      rw [rpow_eq_pow, ← hu]
      have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ u ^ j)
      have h2 : u ^ j ≤ u ^ A.m := pow_le_pow_right₀ hu1 hj.2
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    simp; ring_nf; exact le_refl _
  have hpow : (1 : ℝ) ≤ u ^ A.m := one_le_pow₀ hu1
  have hT' : (T : ℝ) = u * u ^ A.m := by rw [hu, ← pow_succ', u_pow_succ]
  have : (∑ j ∈ Finset.Icc 1 A.m, (A.ceilLen T j : ℝ)) ≤ T := by
    rw [hT']
    refine hsum.trans ?_
    nlinarith
  exact_mod_cast this

/-- `Iᵢ ≤ 2 T^{1/(m+1)} Iᵢ₋₁` and `Iᵢ₋₁ > 0` for `2 ≤ i ≤ m + 1`. -/
theorem ratio (T : ℕ) (hT1 : 1 ≤ T) (i : ℕ) (hi : i ∈ Finset.Icc 2 (A.m + 1)) :
    0 < (A.stageLen T (i - 1) : ℝ) ∧
    (A.stageLen T i : ℝ) ≤ 2 * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) * A.stageLen T (i - 1) := by
  have hi := Finset.mem_Icc.mp hi
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow (by exact_mod_cast hT1) (by positivity)
  have hprev : u ^ (i - 1) ≤ (A.stageLen T (i - 1) : ℝ) := by
    unfold Alg.stageLen
    rw [if_pos (by omega)]
    unfold Alg.ceilLen
    rw [rpow_eq_pow, ← hu]
    exact Nat.le_ceil _
  have hpos : 0 < u ^ (i - 1) := by positivity
  refine ⟨lt_of_lt_of_le hpos hprev, ?_⟩
  have hcur : (A.stageLen T i : ℝ) ≤ 2 * u ^ i := by
    by_cases him : i ≤ A.m
    · unfold Alg.stageLen
      rw [if_pos him]
      unfold Alg.ceilLen
      rw [rpow_eq_pow, ← hu]
      have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ u ^ i)
      have h2 : 1 ≤ u ^ i := one_le_pow₀ hu1
      linarith
    · have hieq : i = A.m + 1 := by omega
      have h1 : A.stageLen T i ≤ T := by
        unfold Alg.stageLen; rw [if_neg him]; omega
      have h2 : (T : ℝ) = u ^ i := by rw [hieq, hu, u_pow_succ]
      have h3 : (A.stageLen T i : ℝ) ≤ T := by exact_mod_cast h1
      have h4 : 0 ≤ u ^ i := by positivity
      linarith
  have hui : u ^ i = u * u ^ (i - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc (A.stageLen T i : ℝ) ≤ 2 * u ^ i := hcur
    _ = 2 * u * u ^ (i - 1) := by rw [hui]; ring
    _ ≤ 2 * u * A.stageLen T (i - 1) :=
      mul_le_mul_of_nonneg_left hprev (by positivity)

theorem expect_sum (z : ℝ) (T : ℕ) (F : Fin T → (Fin T → ℕ) → ENNReal) :
    A.expect z T (fun d => ∑ s : Fin T, F s d) = ∑ s : Fin T, A.expect z T (F s) := by
  unfold Alg.expect
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

end LPC25Aux

namespace LPC25Aux

open LimitedPriceChanges.AlgorithmI

variable {S : Model} (A : Alg S)

/-- `∑_{s : stage ≥ 2} c / I_{stage(s) - 1} ≤ 2 c m T^{1/(m+1)}`. -/
theorem stage_sum_bound (T : ℕ) (hT1 : 1 ≤ T) (hfit : A.stageStart T (A.m + 1) ≤ T)
    (c : ℝ) (hc : 0 ≤ c) :
    ∑ s : Fin T, (if 2 ≤ A.stageOf T s then c / (A.stageLen T (A.stageOf T s - 1) : ℝ) else 0) ≤
      2 * c * A.m * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) := by
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hregroup : ∀ s : Fin T,
      (if 2 ≤ A.stageOf T s then c / (A.stageLen T (A.stageOf T s - 1) : ℝ) else 0) =
      ∑ i ∈ Finset.Icc 2 (A.m + 1),
        (if A.stageOf T s = i then c / (A.stageLen T (i - 1) : ℝ) else 0) := by
    intro s
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_Icc]
    have := stageOf_le A T s
    by_cases h2 : 2 ≤ A.stageOf T s
    · rw [if_pos h2, if_pos ⟨h2, this⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.1)]
  rw [Finset.sum_congr rfl (fun s _ => hregroup s), Finset.sum_comm]
  have hstage : ∀ i ∈ Finset.Icc 2 (A.m + 1),
      ∑ s : Fin T, (if A.stageOf T s = i then c / (A.stageLen T (i - 1) : ℝ) else 0) ≤
        2 * c * u := by
    intro i hi
    obtain ⟨hpos, hrat⟩ := ratio A T hT1 i hi
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard := card_stage A T i hfit (Finset.mem_Icc.mp hi).1
    have hcard' : (((Finset.univ : Finset (Fin T)).filter
        (fun s : Fin T => A.stageOf T (s : ℕ) = i)).card : ℝ) ≤ A.stageLen T i := by
      exact_mod_cast hcard
    calc (((Finset.univ : Finset (Fin T)).filter
          (fun s : Fin T => A.stageOf T (s : ℕ) = i)).card : ℝ) *
          (c / (A.stageLen T (i - 1) : ℝ))
        ≤ (A.stageLen T i : ℝ) * (c / (A.stageLen T (i - 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ ≤ 2 * u * A.stageLen T (i - 1) * (c / (A.stageLen T (i - 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hrat (by positivity)
      _ = 2 * c * u := by field_simp
  refine (Finset.sum_le_sum hstage).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have : ((A.m + 1 + 1 - 2 : ℕ) : ℝ) = A.m := by
    rw [show A.m + 1 + 1 - 2 = A.m by omega]
  rw [this]
  ring_nf
  exact le_refl _

/-- The first stage has at most `2 T^{1/(m+1)}` periods. -/
theorem card_stage_one (T : ℕ) (hT1 : 1 ≤ T) (hm : 1 ≤ A.m) :
    (((Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = 1)).card : ℝ)
      ≤ 2 * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) := by
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow (by exact_mod_cast hT1) (by positivity)
  have hlen : A.stageStart T 2 = A.ceilLen T 1 := by
    unfold Alg.stageStart
    simp [Alg.stageLen, hm]
  have hc : ((Finset.univ : Finset (Fin T)).filter
      (fun s : Fin T => A.stageOf T (s : ℕ) = 1)).card ≤ A.ceilLen T 1 := by
    have := Finset.card_le_card_of_injOn (fun s : Fin T => (s : ℕ))
      (s := (Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = 1))
      (t := Finset.range (A.ceilLen T 1))
      (fun s hs => by
        have hs' : A.stageOf T (s : ℕ) = 1 := by simpa using hs
        simp only [Finset.coe_range, Set.mem_Iio]
        by_contra hge
        push Not at hge
        have hmem : 1 ∈ (Finset.Icc 1 A.m).filter (fun j => A.stageStart T (j + 1) ≤ (s : ℕ)) := by
          rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨le_rfl, hm⟩, by rw [hlen]; exact hge⟩
        have hpos := Finset.card_pos.mpr ⟨1, hmem⟩
        unfold Alg.stageOf at hs'
        omega)
      (fun a _ b _ h => Fin.ext h)
    simpa using this
  have hc' : (A.ceilLen T 1 : ℝ) ≤ 2 * u := by
    unfold Alg.ceilLen
    have : (T : ℝ) ^ (((1 : ℕ) : ℝ) / ((A.m : ℝ) + 1)) = u := by rw [hu]; norm_num
    rw [this]
    have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ u)
    linarith
  calc _ ≤ (A.ceilLen T 1 : ℝ) := by exact_mod_cast hc
    _ ≤ 2 * u := hc'

theorem expect_add (z : ℝ) (T : ℕ) (f g : (Fin T → ℕ) → ENNReal) :
    A.expect z T (fun d => f d + g d) = A.expect z T f + A.expect z T g := by
  unfold Alg.expect
  simp_rw [mul_add]
  exact ENNReal.tsum_add

theorem expect_mono (z : ℝ) (T : ℕ) (f g : (Fin T → ℕ) → ENNReal) (h : ∀ d, f d ≤ g d) :
    A.expect z T f ≤ A.expect z T g := by
  unfold Alg.expect
  exact ENNReal.tsum_le_tsum (fun d => mul_le_mul_right (h d) _)

theorem expect_const_mul (z : ℝ) (T : ℕ) (c : ENNReal) (f : (Fin T → ℕ) → ENNReal) :
    A.expect z T (fun d => c * f d) = c * A.expect z T f := by
  unfold Alg.expect
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext d; ring

theorem expect_ite (z : ℝ) (T : ℕ) (c : ENNReal) (P : (Fin T → ℕ) → Prop) [DecidablePred P] :
    A.expect z T (fun d => if P d then c else 0) = c * A.prob z T {d | P d} := by
  unfold Alg.expect Alg.prob
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext d
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs <;> simp [mul_comm]

theorem expect_finsum {ι : Type*} (z : ℝ) (T : ℕ) (I : Finset ι)
    (F : ι → (Fin T → ℕ) → ENNReal) :
    A.expect z T (fun d => ∑ j ∈ I, F j d) = ∑ j ∈ I, A.expect z T (F j) := by
  unfold Alg.expect
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

end LPC25Aux

namespace LPCThm1Aux

open LimitedPriceChanges.AlgorithmI

theorem uniform_large {ι : Type*} (Y : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ y K K', K ≤ K' → P y K → P y K')
    (h : ∀ y ∈ Y, ∃ K : ℝ, 0 < K ∧ P y K) : ∃ K : ℝ, 0 < K ∧ ∀ y ∈ Y, P y K := by
  classical
  induction Y using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨K, hK, hKs⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    obtain ⟨Ka, hKa, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨max K Ka, lt_max_of_lt_left hK, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hmono _ _ _ (le_max_right _ _) hPa
    · exact hmono _ _ _ (le_max_left _ _) (hKs y hy)

theorem G_le_Gstar (S : Model) (pstar : ℕ → ℝ → ℝ) (z : ℝ) (hz : z ∈ S.Z)
    (hsel : S.IsPriceSelection pstar) (p : ℝ) (hp : p ∈ S.P) (y : ℕ) (hy : y ∈ S.Y) :
    S.G p y z ≤ S.Gstar pstar z := by
  have h1 := (hsel y hy z hz).2 p hp
  have h2 : S.G (pstar y z) y z ≤ S.Gstar pstar z :=
    Finset.le_sup' (fun y => S.G (pstar y z) y z) hy
  linarith

theorem gap_bound (S : Model) (pstar : ℕ → ℝ → ℝ) (z : ℝ) (hS : S.Standing pstar z) :
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S.P, ∀ y ∈ S.Y, S.Gstar pstar z - S.G p y z ≤ B := by
  obtain ⟨c, M, hc, hM, hsd⟩ := hS.assumptionA.second_deriv
  have key : ∀ y ∈ S.Y, ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S.P, S.Gstar pstar z - S.G p y z ≤ B := by
    intro y hy
    have hcont : ContinuousOn (fun p => S.G p y z) (Set.Icc S.pl S.ph) :=
      ((hsd y hy z hS.z_mem (by simpa using hc)).1).continuousOn
    have hne : (Set.Icc S.pl S.ph).Nonempty := ⟨S.pl, Set.left_mem_Icc.mpr S.pl_le_ph⟩
    obtain ⟨p0, hp0, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
    refine ⟨max 1 (S.Gstar pstar z - S.G p0 y z), lt_max_of_lt_left one_pos, fun p hp => ?_⟩
    have := hmin hp
    simp only [Set.mem_ofPred_eq] at this
    linarith [le_max_right 1 (S.Gstar pstar z - S.G p0 y z)]
  obtain ⟨B, hB, hBY⟩ := uniform_large S.Y
    (fun y B => ∀ p ∈ S.P, S.Gstar pstar z - S.G p y z ≤ B)
    (fun y B B' hBB' hP p hp => (hP p hp).trans hBB') key
  exact ⟨B, hB, fun p hp y hy => hBY y hy p hp⟩

end LPCThm1Aux

namespace LPCThm1Aux

open LimitedPriceChanges.AlgorithmI

theorem pointwise (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid)
    (B : ℝ) (hBb : ∀ p ∈ S.P, ∀ y ∈ S.Y, S.Gstar A.pstar z - S.G p y z ≤ B)
    (T : ℕ) (s : Fin T) (d : Fin T → ℕ) :
    ENNReal.ofReal (S.Gstar A.pstar z - S.G (A.price T s d) (A.level T s d) z) ≤
      (if A.stageOf T s = 1 then ENNReal.ofReal B else 0) +
      (if 2 ≤ A.stageOf T s then
          ENNReal.ofReal (S.Gstar A.pstar z -
            S.G (A.phat T (A.stageOf T s) d) (A.yhat T (A.stageOf T s) d) z)
        else 0) +
      (if 2 ≤ A.stageOf T s then
          (if A.yhat T (A.stageOf T s) d ≠ A.ytilde T (A.stageOf T s) d then ENNReal.ofReal B
            else 0)
        else 0) +
      ∑ j ∈ Finset.Icc 2 (A.m + 1), ENNReal.ofReal B *
        (if A.stageOf T s = j ∧ A.level T s d ≠ A.ytilde T j d then (1 : ENNReal) else 0) := by
  have hp := price_mem A z hS hA T s d
  have hl := level_mem A z hS hA T s d
  have hg : S.Gstar A.pstar z - S.G (A.price T s d) (A.level T s d) z ≤ B := hBb _ hp _ hl
  by_cases h1 : A.stageOf T s = 1
  · rw [if_pos h1]
    exact le_add_right (le_add_right (le_add_right (ENNReal.ofReal_le_ofReal hg)))
  · have h2 : 2 ≤ A.stageOf T s := by have := one_le_stageOf A T s; omega
    rw [if_neg h1, if_pos h2, if_pos h2, zero_add]
    set i := A.stageOf T s with hi
    have hpe : A.price T s d = A.phat T i d := rfl
    have hph := phat_mem A z hS hA T i d
    have hyh := yhat_mem A z hS hA T i d
    have hGle := G_le_Gstar S A.pstar z hS.z_mem hS.priceSelection _ hph _ hyh
    have hsplit : S.Gstar A.pstar z - S.G (A.price T s d) (A.level T s d) z =
        (S.Gstar A.pstar z - S.G (A.phat T i d) (A.yhat T i d) z) +
        (S.G (A.phat T i d) (A.yhat T i d) z - S.G (A.price T s d) (A.level T s d) z) := by ring
    rw [hsplit]
    refine (ENNReal.ofReal_add_le).trans ?_
    rw [add_assoc]
    gcongr
    by_cases hlv : A.level T s d = A.yhat T i d
    · rw [hlv, hpe, sub_self, ENNReal.ofReal_zero]; exact zero_le
    · have hb : ENNReal.ofReal (S.G (A.phat T i d) (A.yhat T i d) z -
          S.G (A.price T s d) (A.level T s d) z) ≤ ENNReal.ofReal B :=
        ENNReal.ofReal_le_ofReal (by linarith)
      by_cases hyt : A.yhat T i d ≠ A.ytilde T i d
      · rw [if_pos hyt]; exact le_add_right hb
      · push Not at hyt
        rw [if_neg (not_not.mpr hyt), zero_add]
        have hmem : i ∈ Finset.Icc 2 (A.m + 1) :=
          Finset.mem_Icc.mpr ⟨h2, stageOf_le A T s⟩
        have hterm : ENNReal.ofReal B *
            (if A.stageOf T s = i ∧ A.level T s d ≠ A.ytilde T i d then (1 : ENNReal) else 0) =
            ENNReal.ofReal B := by
          rw [if_pos ⟨rfl, by rw [← hyt]; exact hlv⟩, mul_one]
        refine hb.trans (hterm.symm.le.trans ?_)
        exact Finset.single_le_sum (f := fun j => ENNReal.ofReal B *
          (if A.stageOf T s = j ∧ A.level T s d ≠ A.ytilde T j d then (1 : ENNReal) else 0))
          (fun j _ => zero_le) hmem

end LPCThm1Aux

open LimitedPriceChanges.AlgorithmI in
theorem solution (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z)
    (hA : A.Valid) :
    ∃ K₆ : ℝ, 0 < K₆ ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      A.regret z T ≤ ENNReal.ofReal (K₆ * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1))) := by
  classical
  obtain ⟨K₃₃, hK₃₃, T₁, hT₁⟩ := eq_25 S A z hS hA
  obtain ⟨K₂₆, hK₂₆, T₂, hT₂⟩ := eq_26 S A z hS hA
  obtain ⟨Kc, hKc, T₃, hT₃⟩ := stage_carryover S A z hS hA
  obtain ⟨B, hB, hBb⟩ := LPCThm1Aux.gap_bound S A.pstar z hS
  set m : ℝ := (A.m : ℝ) with hmdef
  have hm1 : (1 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hA.one_le_m
  refine ⟨2 * B + K₃₃ * m + 2 * (B * K₂₆) * m + m * (B * Kc), by positivity,
    max (max T₁ T₂) (max T₃ ((2 * A.m) ^ (A.m + 1) + 1)), fun T hT => ?_⟩
  have hTa : T ≥ T₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTb : T ≥ T₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTc : T ≥ T₃ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTd : (2 * A.m) ^ (A.m + 1) + 1 ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT1 : 1 ≤ T := by omega
  have hfit := LPC25Aux.stages_fit A T hA.one_le_m (by omega)
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow (by exact_mod_cast hT1) (by positivity)
  -- the four parts
  let F1 : ENNReal := ∑ s : Fin T, if A.stageOf T s = 1 then ENNReal.ofReal B else 0
  let F2 : (Fin T → ℕ) → ENNReal := fun d => ∑ s : Fin T,
    if 2 ≤ A.stageOf T s then
      ENNReal.ofReal (S.Gstar A.pstar z -
        S.G (A.phat T (A.stageOf T s) d) (A.yhat T (A.stageOf T s) d) z)
    else 0
  let F3 : (Fin T → ℕ) → ENNReal := fun d => ∑ s : Fin T,
    if 2 ≤ A.stageOf T s then
      (if A.yhat T (A.stageOf T s) d ≠ A.ytilde T (A.stageOf T s) d then ENNReal.ofReal B else 0)
    else 0
  let F4 : (Fin T → ℕ) → ENNReal := fun d => ∑ j ∈ Finset.Icc 2 (A.m + 1),
    ENNReal.ofReal B * ∑ s : Fin T,
      (if A.stageOf T s = j ∧ A.level T s d ≠ A.ytilde T j d then (1 : ENNReal) else 0)
  have hpt : ∀ d, (∑ s : Fin T,
      ENNReal.ofReal (S.Gstar A.pstar z - S.G (A.price T s d) (A.level T s d) z)) ≤
      F1 + F2 d + F3 d + F4 d := by
    intro d
    refine (Finset.sum_le_sum (fun s _ =>
      LPCThm1Aux.pointwise S A z hS hA B hBb T s d)).trans (le_of_eq ?_)
    simp only [F1, F2, F3, F4, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  unfold Alg.regret
  refine (LPC25Aux.expect_mono A z T _ _ hpt).trans ?_
  rw [LPC25Aux.expect_add, LPC25Aux.expect_add, LPC25Aux.expect_add]
  -- part 1
  have hE1 : A.expect z T (fun _ => F1) ≤ ENNReal.ofReal (2 * B * u) := by
    have : A.expect z T (fun _ => F1) = F1 := by
      unfold Alg.expect
      rw [ENNReal.tsum_mul_right, LPCThm1Aux.mass_one A z hS hA T, one_mul]
    rw [this]
    simp only [F1]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hc := LPC25Aux.card_stage_one A T hT1 hA.one_le_m
    rw [← hu] at hc
    calc (((Finset.univ : Finset (Fin T)).filter
          (fun s : Fin T => A.stageOf T (s : ℕ) = 1)).card : ENNReal) * ENNReal.ofReal B
        = ENNReal.ofReal (((Finset.univ : Finset (Fin T)).filter
          (fun s : Fin T => A.stageOf T (s : ℕ) = 1)).card * B) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (2 * B * u) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith
  -- part 2
  have hE2 : A.expect z T F2 ≤ ENNReal.ofReal (K₃₃ * m * u) := hT₁ T hTa
  -- part 3
  have hE3 : A.expect z T F3 ≤ ENNReal.ofReal (2 * (B * K₂₆) * m * u) := by
    simp only [F3]
    rw [LPC25Aux.expect_sum]
    have hs : ∀ s : Fin T, A.expect z T (fun d =>
        if 2 ≤ A.stageOf T s then
          (if A.yhat T (A.stageOf T s) d ≠ A.ytilde T (A.stageOf T s) d then ENNReal.ofReal B
            else 0)
        else 0) ≤ ENNReal.ofReal (if 2 ≤ A.stageOf T s then
          B * K₂₆ / (A.stageLen T (A.stageOf T s - 1) : ℝ) else 0) := by
      intro s
      split_ifs with h2
      · rw [LPC25Aux.expect_ite]
        have hp := hT₂ T hTb (A.stageOf T s) (Finset.mem_Icc.mpr ⟨h2, LPC25Aux.stageOf_le A T s⟩)
        calc ENNReal.ofReal B * A.prob z T {d | A.yhat T (A.stageOf T s) d ≠
              A.ytilde T (A.stageOf T s) d}
            ≤ ENNReal.ofReal B * ENNReal.ofReal (K₂₆ / (A.stageLen T (A.stageOf T s - 1) : ℝ)) :=
              mul_le_mul_right hp _
          _ = ENNReal.ofReal (B * K₂₆ / (A.stageLen T (A.stageOf T s - 1) : ℝ)) := by
              rw [← ENNReal.ofReal_mul hB.le, mul_div_assoc]
      · simp [Alg.expect]
    refine (Finset.sum_le_sum (fun s _ => hs s)).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => by split_ifs <;> positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := LPC25Aux.stage_sum_bound A T hT1 hfit (B * K₂₆) (by positivity)
    rw [← hu] at this
    exact this
  -- part 4
  have hE4 : A.expect z T F4 ≤ ENNReal.ofReal (m * (B * Kc) * u) := by
    simp only [F4]
    rw [LPC25Aux.expect_finsum]
    have hj : ∀ j ∈ Finset.Icc 2 (A.m + 1), A.expect z T (fun d => ENNReal.ofReal B *
        ∑ s : Fin T,
          (if A.stageOf T s = j ∧ A.level T s d ≠ A.ytilde T j d then (1 : ENNReal) else 0)) ≤
        ENNReal.ofReal (B * Kc) := by
      intro j hjm
      rw [LPC25Aux.expect_const_mul, ENNReal.ofReal_mul hB.le]
      apply mul_le_mul_right
      have hjm' : j ∈ Finset.Icc 1 (A.m + 1) := by
        rw [Finset.mem_Icc] at hjm ⊢; omega
      exact hT₃ T hTc j hjm'
    refine (Finset.sum_le_sum hj).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have : ((A.m + 1 + 1 - 2 : ℕ) : ENNReal) = ENNReal.ofReal m := by
      rw [show A.m + 1 + 1 - 2 = A.m by omega, hmdef, ENNReal.ofReal_natCast]
    rw [this, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ m * (B * Kc) := by positivity
    nlinarith
  calc A.expect z T (fun _ => F1) + A.expect z T F2 + A.expect z T F3 + A.expect z T F4
      ≤ ENNReal.ofReal (2 * B * u) + ENNReal.ofReal (K₃₃ * m * u) +
        ENNReal.ofReal (2 * (B * K₂₆) * m * u) + ENNReal.ofReal (m * (B * Kc) * u) := by
        gcongr
    _ = ENNReal.ofReal ((2 * B + K₃₃ * m + 2 * (B * K₂₆) * m + m * (B * Kc)) * u) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
