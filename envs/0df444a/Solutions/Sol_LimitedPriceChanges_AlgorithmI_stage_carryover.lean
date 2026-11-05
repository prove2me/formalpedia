-- Prove2me | solution 1 for LimitedPriceChanges.AlgorithmI.stage_carryover
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:15:37.354623+00:00
-- url     : https://prove2.me/submissions/d871115c-4cf1-45a3-8ba9-9bd8d1affd30

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm

namespace LPCCarryAux

theorem tsum_snoc (T : ℕ) (F : (Fin (T + 1) → ℕ) → ENNReal) :
    ∑' d, F d = ∑' g' : Fin T → ℕ, ∑' a : ℕ, F (Fin.snoc g' a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => ℕ)).tsum_eq, ENNReal.tsum_prod',
    ENNReal.tsum_comm]
  rfl

/-- One-step conditioning for an adapted price process: integrating `φ(d_s)` against the path
law, with an `s`-adapted weight `g`, is the same as integrating the conditional mean. -/
theorem tower (f : ℕ → ℝ → ℝ) (Pset : Set ℝ) (hf0 : ∀ p ∈ Pset, ∀ d, 0 ≤ f d p)
    (hf1 : ∀ p ∈ Pset, HasSum (fun d => f d p) 1) :
    ∀ (T : ℕ) (price : Fin T → (Fin T → ℕ) → ℝ), (∀ s d, price s d ∈ Pset) →
      (∀ s d d', (∀ t : Fin T, t < s → d t = d' t) → price s d = price s d') →
      ∀ (s : Fin T) (g : (Fin T → ℕ) → ENNReal),
      (∀ d d', (∀ t : Fin T, t < s → d t = d' t) → g d = g d') →
      ∀ φ : ℕ → ENNReal,
      ∑' d : Fin T → ℕ, (∏ t, ENNReal.ofReal (f (d t) (price t d))) * (g d * φ (d s)) =
      ∑' d : Fin T → ℕ, (∏ t, ENNReal.ofReal (f (d t) (price t d))) *
        (g d * ∑' a : ℕ, ENNReal.ofReal (f a (price s d)) * φ a) := by
  intro T
  induction T with
  | zero => intro _ _ _ s; exact s.elim0
  | succ T ih =>
    intro price hP hadapt s g hg φ
    let price' : Fin T → (Fin T → ℕ) → ℝ := fun s g => price (Fin.castSucc s) (Fin.snoc g 0)
    let q : (Fin T → ℕ) → ℝ := fun g => price (Fin.last T) (Fin.snoc g 0)
    have hsnoc_eq : ∀ (g' : Fin T → ℕ) (a : ℕ) (t : Fin (T + 1)) (ht : (t : ℕ) < T),
        (Fin.snoc g' a : Fin (T + 1) → ℕ) t = g' ⟨t, ht⟩ := by
      intro g' a t ht
      simp [Fin.snoc, ht, Fin.castLT]
    have hsnoc0 : ∀ (g' : Fin T → ℕ) (a : ℕ) (t : Fin (T + 1)) (ht : (t : ℕ) < T),
        (Fin.snoc g' a : Fin (T + 1) → ℕ) t = (Fin.snoc g' 0 : Fin (T + 1) → ℕ) t := by
      intro g' a t ht
      rw [hsnoc_eq g' a t ht, hsnoc_eq g' 0 t ht]
    have hW : ∀ (g' : Fin T → ℕ) (a : ℕ),
        ∏ t : Fin (T + 1), ENNReal.ofReal (f ((Fin.snoc g' a : Fin (T + 1) → ℕ) t)
          (price t (Fin.snoc g' a))) =
        (∏ t : Fin T, ENNReal.ofReal (f (g' t) (price' t g'))) * ENNReal.ofReal (f a (q g')) := by
      intro g' a
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro t _
        simp only [Fin.snoc_castSucc, price']
        congr 2
        apply hadapt
        intro r hr
        have : (r : ℕ) < T := by
          have := t.isLt
          have h2 : (r : ℕ) < (t : ℕ) := by simpa [Fin.lt_def] using hr
          omega
        exact hsnoc0 g' a r this
      · simp only [Fin.snoc_last, q]
        congr 2
        apply hadapt
        intro r hr
        have : (r : ℕ) < T := by simpa [Fin.lt_def] using hr
        exact hsnoc0 g' a r this
    have hone : ∀ g' : Fin T → ℕ, ∑' a : ℕ, ENNReal.ofReal (f a (q g')) = 1 := by
      intro g'
      have hq : q g' ∈ Pset := hP _ _
      rw [← ENNReal.ofReal_tsum_of_nonneg (hf0 _ hq) (hf1 _ hq).summable, (hf1 _ hq).tsum_eq,
        ENNReal.ofReal_one]
    -- reindex both sides
    rw [tsum_snoc, tsum_snoc]
    simp_rw [hW]
    have hgs : ∀ (g' : Fin T → ℕ) (a : ℕ),
        g (Fin.snoc g' a) = g (Fin.snoc g' 0) := by
      intro g' a
      apply hg
      intro r hr
      have : (r : ℕ) < T := by
        have := s.isLt
        have h2 : (r : ℕ) < (s : ℕ) := Fin.lt_def.mp hr
        omega
      exact hsnoc0 g' a r this
    have hps : ∀ (g' : Fin T → ℕ) (a : ℕ),
        price s (Fin.snoc g' a) = price s (Fin.snoc g' 0) := by
      intro g' a
      apply hadapt
      intro r hr
      have : (r : ℕ) < T := by
        have := s.isLt
        have h2 : (r : ℕ) < (s : ℕ) := Fin.lt_def.mp hr
        omega
      exact hsnoc0 g' a r this
    simp_rw [hgs, hps]
    by_cases hsl : (s : ℕ) = T
    · -- the last coordinate
      have hs : s = Fin.last T := by ext; simp [hsl]
      subst hs
      simp only [Fin.snoc_last]
      apply tsum_congr
      intro g'
      have hq : price (Fin.last T) (Fin.snoc g' 0) = q g' := rfl
      rw [hq]
      set W := ∏ t : Fin T, ENNReal.ofReal (f (g' t) (price' t g'))
      set G := g (Fin.snoc g' 0)
      have e1 : ∑' a, W * ENNReal.ofReal (f a (q g')) * (G * φ a) =
          W * G * ∑' a, ENNReal.ofReal (f a (q g')) * φ a := by
        rw [← ENNReal.tsum_mul_left]; congr 1; ext a; ring
      have e2 : ∑' a, W * ENNReal.ofReal (f a (q g')) *
          (G * ∑' b, ENNReal.ofReal (f b (q g')) * φ b) =
          W * G * ∑' b, ENNReal.ofReal (f b (q g')) * φ b := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hone]; ring
      rw [e1, e2]
    · -- an earlier coordinate
      have hsT : (s : ℕ) < T := by have := s.isLt; omega
      set s' : Fin T := ⟨s, hsT⟩
      have hφ : ∀ (g' : Fin T → ℕ) (a : ℕ),
          (Fin.snoc g' a : Fin (T + 1) → ℕ) s = g' s' := by
        intro g' a
        exact hsnoc_eq g' a s hsT
      simp_rw [hφ]
      have hpq : ∀ g' : Fin T → ℕ, price s (Fin.snoc g' 0) = price' s' g' := by
        intro g'
        simp only [price']
        congr 1
      simp_rw [hpq]
      have hL : ∀ g' : Fin T → ℕ, ∀ X : ENNReal,
          ∑' a, (∏ t : Fin T, ENNReal.ofReal (f (g' t) (price' t g'))) *
            ENNReal.ofReal (f a (q g')) * X =
          (∏ t : Fin T, ENNReal.ofReal (f (g' t) (price' t g'))) * X := by
        intro g' X
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hone, mul_one]
      simp_rw [hL]
      apply ih price' (fun _ _ => hP _ _) _ s' (fun g' => g (Fin.snoc g' 0))
      · intro g₁ g₂ h
        apply hg
        intro r hr
        have : (r : ℕ) < T := by
          have h2 : (r : ℕ) < (s : ℕ) := Fin.lt_def.mp hr
          omega
        rw [hsnoc_eq g₁ 0 r this, hsnoc_eq g₂ 0 r this]
        apply h
        exact Fin.lt_def.mpr (Fin.lt_def.mp hr)
      · intro t g₁ g₂ h
        simp only [price']
        apply hadapt
        intro r hr
        by_cases hrT : (r : ℕ) < T
        · rw [hsnoc_eq g₁ 0 r hrT, hsnoc_eq g₂ 0 r hrT]
          apply h
          simpa [Fin.lt_def] using hr
        · exfalso
          have := t.isLt
          simp [Fin.lt_def] at hr
          omega

end LPCCarryAux

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

namespace LPCCarryAux

open LimitedPriceChanges.AlgorithmI

theorem runStage_last (d : ℕ → ℕ) (ytil : ℕ) : ∀ k s0 x,
    (Alg.runStage d ytil s0 (k + 1) x).2 =
      max (Alg.runStage d ytil s0 k x).2 ytil -
        min (d (s0 + k)) (max (Alg.runStage d ytil s0 k x).2 ytil) := by
  intro k
  induction k with
  | zero => intro s0 x; simp [Alg.runStage]
  | succ k ih =>
    intro s0 x
    have h1 : (Alg.runStage d ytil s0 (k + 1 + 1) x).2 =
        (Alg.runStage d ytil (s0 + 1) (k + 1) (max x ytil - min (d s0) (max x ytil))).2 := by
      simp [Alg.runStage]
    have h2 : (Alg.runStage d ytil s0 (k + 1) x).2 =
        (Alg.runStage d ytil (s0 + 1) k (max x ytil - min (d s0) (max x ytil))).2 := by
      simp [Alg.runStage]
    rw [h1, h2, ih]
    rw [show s0 + 1 + k = s0 + (k + 1) by omega]

/-- Potential argument: periods with inventory above the target and positive demand are at most
the initial excess. -/
theorem count_le (d : ℕ → ℕ) (ytil s0 x : ℕ) : ∀ L,
    ((Finset.range L).filter (fun k => ytil < (Alg.runStage d ytil s0 k x).2 ∧
      1 ≤ d (s0 + k))).card + ((Alg.runStage d ytil s0 L x).2 - ytil) ≤ x - ytil := by
  intro L
  induction L with
  | zero => simp [Alg.runStage]
  | succ L ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have hL : L ∉ (Finset.range L).filter (fun k => ytil < (Alg.runStage d ytil s0 k x).2 ∧
        1 ≤ d (s0 + k)) := by simp
    rw [runStage_last]
    set X := (Alg.runStage d ytil s0 L x).2
    split_ifs with hc
    · rw [Finset.card_insert_of_notMem hL]
      have hmax : max X ytil = X := max_eq_left hc.1.le
      rw [hmax]
      have : min (d (s0 + L)) X ≥ 1 := le_min hc.2 (by omega)
      omega
    · by_cases hX : ytil < X
      · have hd : d (s0 + L) = 0 := by
          by_contra h; exact hc ⟨hX, by omega⟩
        rw [max_eq_left hX.le, hd]
        simpa using ih
      · push Not at hX
        rw [max_eq_right hX]
        have : ytil - min (d (s0 + L)) ytil - ytil = 0 := by omega
        rw [this]
        omega

end LPCCarryAux

namespace LPCCarryAux

open LimitedPriceChanges.AlgorithmI LPCThm1Aux

variable {S : Model} (A : Alg S)

theorem level_eq (T : ℕ) (s : Fin T) (d : Fin T → ℕ) (i : ℕ) (hi : A.stageOf T s = i) :
    A.level T s d = max (Alg.runStage (Alg.extend d) (A.ytilde T i d) (A.stageStart T i)
      ((s : ℕ) - A.stageStart T i) (A.stageState T (Alg.extend d) (i - 1)).2.2).2
      (A.ytilde T i d) := by
  subst hi; rfl

theorem g_adapted (T i : ℕ) (s : Fin T) (d d' : Fin T → ℕ)
    (h : ∀ t : Fin T, t < s → d t = d' t) :
    (if A.stageOf T s = i ∧ A.level T s d ≠ A.ytilde T i d then (1 : ENNReal) else 0) =
    (if A.stageOf T s = i ∧ A.level T s d' ≠ A.ytilde T i d' then (1 : ENNReal) else 0) := by
  by_cases hi : A.stageOf T s = i
  · have hle : A.stageStart T i ≤ s := hi ▸ stageStart_stageOf_le A T s
    have hi1 : 1 ≤ i := hi ▸ one_le_stageOf A T s
    have hext : ∀ t, t < (s : ℕ) → Alg.extend d t = Alg.extend d' t := by
      intro t ht
      have htT : t < T := lt_trans ht s.isLt
      simp only [Alg.extend, dif_pos htT]
      exact h ⟨t, htT⟩ (Fin.lt_def.mpr ht)
    have hst : A.stageState T (Alg.extend d) (i - 1) = A.stageState T (Alg.extend d') (i - 1) := by
      apply stageState_congr
      intro t ht
      rw [show i - 1 + 1 = i by omega] at ht
      exact hext t (by omega)
    have hyt : A.ytilde T i d = A.ytilde T i d' := by
      unfold Alg.ytilde Alg.yhat; rw [hst]
    have hlev : A.level T s d = A.level T s d' := by
      rw [level_eq A T s d i hi, level_eq A T s d' i hi, hyt, hst,
        runStage_congr (Alg.extend d) (Alg.extend d') _ _ _ _ (fun t _ ht2 => hext t (by omega))]
    rw [hlev, hyt]
  · simp [hi]

/-- Deterministic bound: carried-over periods with positive demand are at most `yh`. -/
theorem det_count (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T i : ℕ)
    (d : Fin T → ℕ) :
    ((Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = i ∧
      A.level T s d ≠ A.ytilde T i d ∧ 1 ≤ d s)).card ≤ S.yh := by
  have hx₀ : (A.stageState T (Alg.extend d) (i - 1)).2.2 ≤ S.yh :=
    (stageState_mem A z hS hA T _ _).2.2
  have hc := count_le (Alg.extend d) (A.ytilde T i d) (A.stageStart T i)
    (A.stageState T (Alg.extend d) (i - 1)).2.2 T
  have hinj := Finset.card_le_card_of_injOn (fun s : Fin T => (s : ℕ) - A.stageStart T i)
    (s := (Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = i ∧
      A.level T s d ≠ A.ytilde T i d ∧ 1 ≤ d s))
    (t := (Finset.range T).filter (fun k => A.ytilde T i d < (Alg.runStage (Alg.extend d)
      (A.ytilde T i d) (A.stageStart T i) k (A.stageState T (Alg.extend d) (i - 1)).2.2).2 ∧
      1 ≤ Alg.extend d (A.stageStart T i + k)))
    (fun s hs => by
      have hs' : A.stageOf T (s : ℕ) = i ∧ A.level T s d ≠ A.ytilde T i d ∧ 1 ≤ d s := by
        simpa using hs
      have hle : A.stageStart T i ≤ s := by
        have := stageStart_stageOf_le A T s; rw [hs'.1] at this; exact this
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      refine ⟨by omega, ?_, ?_⟩
      · have hl := hs'.2.1
        rw [level_eq A T s d i hs'.1] at hl
        by_contra hn
        exact hl (max_eq_right (not_lt.mp hn))
      · rw [show A.stageStart T i + ((s : ℕ) - A.stageStart T i) = s by omega]
        simp only [Alg.extend, dif_pos s.isLt]
        exact hs'.2.2)
    (fun a ha b hb hab => by
      have ha' : A.stageOf T (a : ℕ) = i := by simp at ha; exact ha.1
      have hb' : A.stageOf T (b : ℕ) = i := by simp at hb; exact hb.1
      have hla : A.stageStart T i ≤ a := by
        have := stageStart_stageOf_le A T a; rw [ha'] at this; exact this
      have hlb : A.stageStart T i ≤ b := by
        have := stageStart_stageOf_le A T b; rw [hb'] at this; exact this
      simp only at hab
      ext; omega)
  omega

end LPCCarryAux

open LimitedPriceChanges.AlgorithmI LPCThm1Aux LPCCarryAux in
theorem solution (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z)
    (hA : A.Valid) :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ i ∈ Finset.Icc 1 (A.m + 1),
      A.expect z T (fun d => ∑ s : Fin T,
          if A.stageOf T s = i ∧ A.level T s d ≠ A.ytilde T i d then (1 : ENNReal) else 0) ≤
        ENNReal.ofReal K := by
  classical
  obtain ⟨c₅, hc₅, hf_ge⟩ := hS.assumption1.f_ge
  -- `yh ≥ 1`
  have hyh1 : 1 ≤ S.yh := by
    obtain ⟨y, hy, hyopt⟩ := Finset.exists_mem_eq_sup' S.Y_nonempty
      (fun y => S.G (A.pstar y z) y z)
    have h1 := hS.optLevel y hy hyopt.symm
    simp only [Model.Y, Finset.mem_Icc] at hy
    omega
  -- `f(0; p, z) ≤ 1 - c₅`
  have hzero : ∀ p ∈ S.P, S.f 0 p z ≤ 1 - c₅ := by
    intro p hp
    set d₁ := max S.dl 1
    have hd₁ : c₅ ≤ S.f d₁ p z := hf_ge p hp z hS.z_mem d₁ (le_max_left _ _)
      (max_le (by have := S.dl_le_yl; have := S.yl_le_yh; omega) hyh1)
    have hne : (0 : ℕ) ≠ d₁ := by have := le_max_right S.dl 1; omega
    have hsum := sum_le_hasSum ({0, d₁} : Finset ℕ)
      (fun j _ => S.f_nonneg p hp z hS.z_mem j) (S.f_hasSum p hp z hS.z_mem)
    rw [Finset.sum_pair hne] at hsum
    linarith
  have hc₅1 : c₅ ≤ 1 := by
    have := hzero S.pl (Set.left_mem_Icc.mpr S.pl_le_ph)
    have := S.f_nonneg S.pl (Set.left_mem_Icc.mpr S.pl_le_ph) z hS.z_mem 0
    linarith
  refine ⟨(S.yh : ℝ) / c₅ + 1, by positivity, 0, fun T _ i hi => ?_⟩
  set g : Fin T → (Fin T → ℕ) → ENNReal := fun s d =>
    if A.stageOf T s = i ∧ A.level T s d ≠ A.ytilde T i d then (1 : ENNReal) else 0 with hg
  set w := A.pathWeight z T with hw
  have hmass : ∑' d, w d = 1 := mass_one A z hS hA T
  let φ₀ : ℕ → ENNReal := fun a => if a = 0 then 1 else 0
  let φ₁ : ℕ → ENNReal := fun a => if 1 ≤ a then 1 else 0
  have hsplit : ∀ s d, g s d = g s d * φ₁ (d s) + g s d * φ₀ (d s) := by
    intro s d
    simp only [φ₀, φ₁]
    by_cases h : d s = 0
    · simp [h]
    · have : 1 ≤ d s := by omega
      simp [h, this]
  set E := A.expect z T (fun d => ∑ s, g s d) with hE
  have hEdef : E = ∑' d, w d * ∑ s, g s d := rfl
  -- finiteness
  have hEfin : E ≠ ⊤ := by
    have : E ≤ T := by
      rw [hEdef]
      calc ∑' d, w d * ∑ s, g s d ≤ ∑' d, w d * (T : ENNReal) := by
            gcongr with d
            calc ∑ s, g s d ≤ ∑ _s : Fin T, (1 : ENNReal) :=
                  Finset.sum_le_sum (fun s _ => by simp only [hg]; split_ifs <;> simp)
              _ = T := by simp
        _ = T := by rw [ENNReal.tsum_mul_right, hmass, one_mul]
    exact ne_top_of_le_ne_top (by simp) this
  -- the positive-demand part
  have hpart1 : ∀ d, ∑ s, g s d * φ₁ (d s) ≤ (S.yh : ENNReal) := by
    intro d
    have heq : ∀ s : Fin T, g s d * φ₁ (d s) =
        if (A.stageOf T (s : ℕ) = i ∧ A.level T s d ≠ A.ytilde T i d ∧ 1 ≤ d s) then 1 else 0 := by
      intro s
      simp only [hg, φ₁]
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl (fun s _ => heq s), Finset.sum_boole]
    exact_mod_cast det_count A z hS hA T i d
  -- the zero-demand part, by one-step conditioning
  have hpart0 : ∀ s : Fin T, ∑' d, w d * (g s d * φ₀ (d s)) ≤
      ENNReal.ofReal (1 - c₅) * ∑' d, w d * g s d := by
    intro s
    have ht := tower (fun a p => S.f a p z) S.P (fun p hp a => S.f_nonneg p hp z hS.z_mem a)
      (fun p hp => S.f_hasSum p hp z hS.z_mem) T (fun s d => A.price T s d)
      (fun s d => price_mem A z hS hA T s d) (fun s d d' h => price_adapted A T s d d' h)
      s (g s) (fun d d' h => g_adapted A T i s d d' h) φ₀
    have hwd : ∀ d, w d = ∏ t, ENNReal.ofReal ((fun a p => S.f a p z) (d t) (A.price T t d)) :=
      fun d => rfl
    simp_rw [hwd]
    rw [ht]
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro d
    have hφ : ∑' a, ENNReal.ofReal (S.f a (A.price T s d) z) * φ₀ a =
        ENNReal.ofReal (S.f 0 (A.price T s d) z) := by
      rw [tsum_eq_single 0]
      · simp [φ₀]
      · intro a ha; simp [φ₀, ha]
    rw [hφ]
    have hle : ENNReal.ofReal (S.f 0 (A.price T s d) z) ≤ ENNReal.ofReal (1 - c₅) :=
      ENNReal.ofReal_le_ofReal (hzero _ (price_mem A z hS hA T s d))
    calc (∏ t, ENNReal.ofReal (S.f (d t) (A.price T t d) z)) *
          (g s d * ENNReal.ofReal (S.f 0 (A.price T s d) z))
        ≤ (∏ t, ENNReal.ofReal (S.f (d t) (A.price T t d) z)) *
          (g s d * ENNReal.ofReal (1 - c₅)) := by gcongr
      _ = ENNReal.ofReal (1 - c₅) *
          ((∏ t, ENNReal.ofReal (S.f (d t) (A.price T t d) z)) * g s d) := by ring
  -- combine
  have hmain : E ≤ (S.yh : ENNReal) + ENNReal.ofReal (1 - c₅) * E := by
    have h1 : ∀ d, w d * ∑ s, g s d =
        w d * ∑ s, g s d * φ₁ (d s) + ∑ s, w d * (g s d * φ₀ (d s)) := by
      intro d
      rw [← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun s _ => hsplit s d)
    calc E = ∑' d, (w d * ∑ s, g s d * φ₁ (d s) + ∑ s, w d * (g s d * φ₀ (d s))) := by
          rw [hEdef]; exact tsum_congr h1
      _ = ∑' d, w d * ∑ s, g s d * φ₁ (d s) + ∑ s, ∑' d, w d * (g s d * φ₀ (d s)) := by
          rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      _ ≤ (S.yh : ENNReal) + ENNReal.ofReal (1 - c₅) * E := by
          gcongr
          · calc ∑' d, w d * ∑ s, g s d * φ₁ (d s) ≤ ∑' d, w d * (S.yh : ENNReal) := by
                  gcongr with d; exact hpart1 d
              _ = S.yh := by rw [ENNReal.tsum_mul_right, hmass, one_mul]
          · calc ∑ s, ∑' d, w d * (g s d * φ₀ (d s))
                ≤ ∑ s, ENNReal.ofReal (1 - c₅) * ∑' d, w d * g s d :=
                  Finset.sum_le_sum (fun s _ => hpart0 s)
              _ = ENNReal.ofReal (1 - c₅) * E := by
                  rw [hEdef, ← Finset.mul_sum,
                    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
                  simp_rw [Finset.mul_sum]
  -- solve the linear inequality
  have hEeq : E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hEfin).symm
  have hE0 : 0 ≤ E.toReal := ENNReal.toReal_nonneg
  rw [hEeq] at hmain
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (by positivity) (by nlinarith)] at hmain
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).mp hmain
  have hbound : E.toReal ≤ (S.yh : ℝ) / c₅ := by
    rw [le_div_iff₀ hc₅]; nlinarith
  calc A.expect z T (fun d => ∑ s : Fin T,
        if A.stageOf T s = i ∧ A.level T s d ≠ A.ytilde T i d then (1 : ENNReal) else 0)
      = E := rfl
    _ = ENNReal.ofReal E.toReal := hEeq
    _ ≤ ENNReal.ofReal ((S.yh : ℝ) / c₅ + 1) := ENNReal.ofReal_le_ofReal (by linarith)
