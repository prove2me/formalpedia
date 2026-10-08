-- Prove2me | solution 1 for IgnallSchrage.Invariance.location_scale_invariance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:31:42.085682+00:00
-- url     : https://prove2.me/submissions/52777262-d53c-4edb-acd6-3024ef7df576

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_Procedure
import Definitions.Def_IgnallSchrage_Invariance_ThreeMachine
import Definitions.Def_IgnallSchrage_Invariance_TwoMachine



namespace IgnallSchrage.Invariance

open JohnsonFlowShop

theorem my_asapDone_succ {n : ℕ} (a b c : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (m : ℕ) (h : m < n) :
    ThreeStage.asapDone a b c σ (m+1) =
      ((ThreeStage.asapDone a b c σ m).1 + a (σ ⟨m, h⟩),
       max (ThreeStage.asapDone a b c σ m).2.1 ((ThreeStage.asapDone a b c σ m).1 + a (σ ⟨m, h⟩)) + b (σ ⟨m, h⟩),
       max (ThreeStage.asapDone a b c σ m).2.2
         (max (ThreeStage.asapDone a b c σ m).2.1 ((ThreeStage.asapDone a b c σ m).1 + a (σ ⟨m, h⟩)) + b (σ ⟨m, h⟩))
         + c (σ ⟨m, h⟩)) := by
  rw [ThreeStage.asapDone, dif_pos h]

theorem my_asapDone_scale {n : ℕ} (a b c : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    ThreeStage.asapDone (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) σ m =
      (H * (ThreeStage.asapDone a b c σ m).1, H * (ThreeStage.asapDone a b c σ m).2.1,
        H * (ThreeStage.asapDone a b c σ m).2.2) := by
  induction m with
  | zero => simp [ThreeStage.asapDone]
  | succ m ih =>
    by_cases h : m < n
    · rw [my_asapDone_succ _ _ _ _ _ h, my_asapDone_succ _ _ _ _ _ h, ih]
      simp only [Prod.mk.injEq]
      refine ⟨by ring, ?_, ?_⟩
      · rw [← mul_add, ← mul_max_of_nonneg _ _ hH.le]; ring
      · rw [← mul_add, ← mul_max_of_nonneg _ _ hH.le, ← mul_add, ← mul_max_of_nonneg _ _ hH.le]; ring
    · simp only [ThreeStage.asapDone, dif_neg h]; exact ih

theorem my_asapDone_shift {n : ℕ} (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) (r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    ThreeStage.asapDone (fun i => a i + G) (fun i => b i + G) (fun i => c i + G) σ r =
      ((ThreeStage.asapDone a b c σ r).1 + r * G,
       (ThreeStage.asapDone a b c σ r).2.1 + (r + 1) * G,
       (ThreeStage.asapDone a b c σ r).2.2 + (r + 2) * G) := by
  induction r, hr1 using Nat.le_induction with
  | base =>
    have h0 : 0 < n := hrn
    rw [my_asapDone_succ _ _ _ _ _ h0, my_asapDone_succ _ _ _ _ _ h0]
    have e : ThreeStage.asapDone a b c σ 0 = (0,0,0) := by simp [ThreeStage.asapDone]
    have e' : ∀ (a b c : Fin n → ℝ), ThreeStage.asapDone a b c σ 0 = (0,0,0) := by
      intro a b c; simp [ThreeStage.asapDone]
    rw [e', e']
    have h1 := ha (σ ⟨0, h0⟩); have h2 := hb (σ ⟨0, h0⟩); have h3 := hc (σ ⟨0, h0⟩)
    simp only [Prod.mk.injEq]
    refine ⟨by push_cast; ring, ?_, ?_⟩ <;> (simp only [max_def]; split_ifs <;> push_cast <;> linarith)
  | succ r hr ih =>
    have hr' : r ≤ n := by omega
    have hrn' : r < n := by omega
    rw [my_asapDone_succ _ _ _ _ _ hrn', my_asapDone_succ _ _ _ _ _ hrn', ih hr']
    simp only [Prod.mk.injEq]
    refine ⟨by push_cast; ring, ?_, ?_⟩ <;> (simp only [max_def]; split_ifs <;> push_cast <;> linarith)


theorem my_asapC2_succ {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (m : ℕ) (h : m < n) :
    TwoStage.asapC2 a b σ (m+1) =
      max (∑ l ∈ Finset.Iic (⟨m, h⟩ : Fin n), a (σ l)) (TwoStage.asapC2 a b σ m) + b (σ ⟨m, h⟩) := by
  rw [TwoStage.asapC2, dif_pos h]

theorem my_asapC2_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    TwoStage.asapC2 (fun i => H * a i) (fun i => H * b i) σ m = H * TwoStage.asapC2 a b σ m := by
  induction m with
  | zero => simp [TwoStage.asapC2]
  | succ m ih =>
    by_cases h : m < n
    · rw [my_asapC2_succ _ _ _ _ h, my_asapC2_succ _ _ _ _ h, ih, ← Finset.mul_sum, mul_add,
        mul_max_of_nonneg _ _ hH.le]
    · simp only [TwoStage.asapC2, dif_neg h]; exact ih

theorem my_asapC2_shift {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) (r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    TwoStage.asapC2 (fun i => a i + G) (fun i => b i + G) σ r =
      TwoStage.asapC2 a b σ r + (r + 1) * G := by
  induction r, hr1 using Nat.le_induction with
  | base =>
    have h0 : 0 < n := hrn
    rw [my_asapC2_succ _ _ _ _ h0, my_asapC2_succ _ _ _ _ h0]
    have e : ∀ (a b : Fin n → ℝ), TwoStage.asapC2 a b σ 0 = 0 := by
      intro a b; simp [TwoStage.asapC2]
    rw [e, e]
    have hs : ∑ l ∈ Finset.Iic (⟨0, h0⟩ : Fin n), a (σ l) = a (σ ⟨0, h0⟩) := by
      have : Finset.Iic (⟨0, h0⟩ : Fin n) = {⟨0, h0⟩} := by
        ext x; simp [Fin.le_def, Fin.ext_iff]
      rw [this]; simp
    have hs' : ∑ l ∈ Finset.Iic (⟨0, h0⟩ : Fin n), (a (σ l) + G) = a (σ ⟨0, h0⟩) + G := by
      have : Finset.Iic (⟨0, h0⟩ : Fin n) = {⟨0, h0⟩} := by
        ext x; simp [Fin.le_def, Fin.ext_iff]
      rw [this]; simp
    rw [hs, hs']
    have h1 := ha (σ ⟨0, h0⟩); have h2 := hb (σ ⟨0, h0⟩)
    simp only [max_def]; split_ifs <;> push_cast <;> linarith
  | succ r hr ih =>
    have hr' : r ≤ n := by omega
    have hrn' : r < n := by omega
    rw [my_asapC2_succ _ _ _ _ hrn', my_asapC2_succ _ _ _ _ hrn', ih hr']
    have hs : ∑ l ∈ Finset.Iic (⟨r, hrn'⟩ : Fin n), (a (σ l) + G) =
        ∑ l ∈ Finset.Iic (⟨r, hrn'⟩ : Fin n), a (σ l) + (r + 1) * G := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Fin.card_Iic]; simp
    rw [hs]
    simp only [max_def]; split_ifs <;> push_cast <;> linarith

theorem my_makespan_scale {n : ℕ} (a b c : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (σ : Equiv.Perm (Fin n)) :
    IgnallSchrage.Makespan.makespan (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) σ =
      H * IgnallSchrage.Makespan.makespan a b c σ := by
  unfold IgnallSchrage.Makespan.makespan
  rw [my_asapDone_scale _ _ _ _ hH]

theorem my_makespan_shift {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) :
    IgnallSchrage.Makespan.makespan (fun i => a i + G) (fun i => b i + G) (fun i => c i + G) σ =
      IgnallSchrage.Makespan.makespan a b c σ + G * (n + 2) := by
  unfold IgnallSchrage.Makespan.makespan
  rw [my_asapDone_shift a b c ha hb hc G hG σ n hn le_rfl]
  ring

theorem my_sumCompletion_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (σ : Equiv.Perm (Fin n)) :
    sumCompletion (fun i => H * a i) (fun i => H * b i) σ = H * sumCompletion a b σ := by
  unfold sumCompletion
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => my_asapC2_scale a b H hH σ _)

theorem my_sumCompletion_shift {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) :
    sumCompletion (fun i => a i + G) (fun i => b i + G) σ =
      sumCompletion a b σ + G * n * (n + 3) / 2 := by
  unfold sumCompletion
  have : ∀ k : Fin n, TwoStage.asapC2 (fun i => a i + G) (fun i => b i + G) σ (k.val + 1) =
      TwoStage.asapC2 a b σ (k.val + 1) + ((k.val : ℝ) + 2) * G := by
    intro k
    rw [my_asapC2_shift a b ha hb G hG σ (k.val + 1) (by omega) k.2]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun k => ((k : ℝ) + 2)) n]
  have : ∀ m : ℕ, ∑ k ∈ Finset.range m, ((k : ℝ) + 2) = (m : ℝ) * ((m : ℝ) + 3) / 2 := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [this]; ring


theorem my_inf'_add_const {α : Type*} {s : Finset α} (h : s.Nonempty) (f : α → ℝ) (k : ℝ) :
    s.inf' h (fun x => f x + k) = s.inf' h f + k := by
  obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_inf' h f
  apply le_antisymm
  · calc s.inf' h (fun x => f x + k) ≤ f i + k := Finset.inf'_le _ hi
      _ = _ := by rw [hfi]
  · apply Finset.le_inf'
    intro j hj
    have := Finset.inf'_le f hj
    linarith

theorem my_inf'_mul_const {α : Type*} {s : Finset α} (h : s.Nonempty) (f : α → ℝ) (H : ℝ) (hH : 0 < H) :
    s.inf' h (fun x => H * f x) = H * s.inf' h f := by
  obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_inf' h f
  apply le_antisymm
  · calc s.inf' h (fun x => H * f x) ≤ H * f i := Finset.inf'_le _ hi
      _ = _ := by rw [hfi]
  · apply Finset.le_inf'
    intro j hj
    have := Finset.inf'_le f hj
    exact mul_le_mul_of_nonneg_left this hH.le

theorem my_minOver_add_const {n : ℕ} {U : Finset (Fin n)} (h : U.Nonempty) (f : Fin n → ℝ) (k : ℝ) :
    IgnallSchrage.Makespan.minOver U (fun i => f i + k) = IgnallSchrage.Makespan.minOver U f + k := by
  unfold IgnallSchrage.Makespan.minOver
  rw [dif_pos h, dif_pos h, my_inf'_add_const]

theorem my_minOver_mul_const {n : ℕ} (U : Finset (Fin n)) (f : Fin n → ℝ) (H : ℝ) (hH : 0 < H) :
    IgnallSchrage.Makespan.minOver U (fun i => H * f i) = H * IgnallSchrage.Makespan.minOver U f := by
  unfold IgnallSchrage.Makespan.minOver
  by_cases h : U.Nonempty
  · rw [dif_pos h, dif_pos h, my_inf'_mul_const]; exact hH
  · rw [dif_neg h, dif_neg h]; simp

theorem my_appendJob3_scale {n : ℕ} (a b c : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (t : ℝ × ℝ × ℝ) (i : Fin n) :
    appendJob3 (fun i => H * a i) (fun i => H * b i) (fun i => H * c i)
        (H * t.1, H * t.2.1, H * t.2.2) i =
      (H * (appendJob3 a b c t i).1, H * (appendJob3 a b c t i).2.1, H * (appendJob3 a b c t i).2.2) := by
  simp only [appendJob3, Prod.mk.injEq]
  refine ⟨by ring, ?_, ?_⟩
  · rw [← mul_add, ← mul_max_of_nonneg _ _ hH.le]; ring
  · rw [← mul_add, ← mul_max_of_nonneg _ _ hH.le, ← mul_add, ← mul_max_of_nonneg _ _ hH.le]; ring

theorem my_foldl3_scale {n : ℕ} (a b c : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J : List (Fin n)) :
    ∀ t : ℝ × ℝ × ℝ,
    J.foldl (appendJob3 (fun i => H * a i) (fun i => H * b i) (fun i => H * c i))
        (H * t.1, H * t.2.1, H * t.2.2) =
      (H * (J.foldl (appendJob3 a b c) t).1, H * (J.foldl (appendJob3 a b c) t).2.1,
        H * (J.foldl (appendJob3 a b c) t).2.2) := by
  induction J with
  | nil => intro t; simp
  | cons j J ih =>
    intro t
    simp only [List.foldl_cons]
    rw [my_appendJob3_scale a b c H hH t j]
    exact ih _

theorem my_times3_scale {n : ℕ} (a b c : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J : List (Fin n)) :
    times3 (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) J =
      (H * (times3 a b c J).1, H * (times3 a b c J).2.1, H * (times3 a b c J).2.2) := by
  unfold times3
  have := my_foldl3_scale a b c H hH J (0, 0, 0)
  simpa using this

theorem my_lowerBound3_scale {n : ℕ} (a b c : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J : List (Fin n)) :
    lowerBound3 (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) J =
      H * lowerBound3 a b c J := by
  simp only [lowerBound3]
  rw [my_times3_scale a b c H hH J]
  have e1 : (fun i => H * b i + H * c i) = fun i => H * (b i + c i) := by funext i; ring
  rw [e1, my_minOver_mul_const _ _ _ hH, my_minOver_mul_const _ _ _ hH, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [mul_max_of_nonneg _ _ hH.le]
  congr 1 <;> [skip; congr 1] <;> ring_nf

theorem my_foldl3_shift {n : ℕ} (a b c : Fin n → ℝ) (G : ℝ) (J : List (Fin n)) :
    ∀ (t : ℝ × ℝ × ℝ) (s : ℕ),
    J.foldl (appendJob3 (fun i => a i + G) (fun i => b i + G) (fun i => c i + G))
        (t.1 + s * G, t.2.1 + (s + 1) * G, t.2.2 + (s + 2) * G) =
      ((J.foldl (appendJob3 a b c) t).1 + (s + J.length : ℕ) * G,
       (J.foldl (appendJob3 a b c) t).2.1 + ((s + J.length : ℕ) + 1) * G,
       (J.foldl (appendJob3 a b c) t).2.2 + ((s + J.length : ℕ) + 2) * G) := by
  induction J with
  | nil => intro t s; simp
  | cons j J ih =>
    intro t s
    simp only [List.foldl_cons]
    have : appendJob3 (fun i => a i + G) (fun i => b i + G) (fun i => c i + G)
        (t.1 + s * G, t.2.1 + (s + 1) * G, t.2.2 + (s + 2) * G) j =
        ((appendJob3 a b c t j).1 + ((s + 1 : ℕ) : ℝ) * G,
         (appendJob3 a b c t j).2.1 + (((s + 1 : ℕ) : ℝ) + 1) * G,
         (appendJob3 a b c t j).2.2 + (((s + 1 : ℕ) : ℝ) + 2) * G) := by
      simp only [appendJob3, Prod.mk.injEq]
      refine ⟨by push_cast; ring, ?_, ?_⟩ <;>
        (simp only [max_def]; split_ifs <;> push_cast <;> linarith)
    rw [this, ih]
    simp only [List.length_cons]
    have : s + 1 + J.length = s + (J.length + 1) := by omega
    rw [this]

theorem my_times3_shift {n : ℕ} (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (G : ℝ) (hG : 0 < G)
    (J : List (Fin n)) (hJ : 1 ≤ J.length) :
    times3 (fun i => a i + G) (fun i => b i + G) (fun i => c i + G) J =
      ((times3 a b c J).1 + (J.length : ℝ) * G,
       (times3 a b c J).2.1 + ((J.length : ℝ) + 1) * G,
       (times3 a b c J).2.2 + ((J.length : ℝ) + 2) * G) := by
  cases J with
  | nil => simp at hJ
  | cons j J =>
    unfold times3
    simp only [List.foldl_cons]
    have h1 := ha j; have h2 := hb j; have h3 := hc j
    have : appendJob3 (fun i => a i + G) (fun i => b i + G) (fun i => c i + G) (0, 0, 0) j =
        ((appendJob3 a b c (0,0,0) j).1 + ((1:ℕ):ℝ) * G,
         (appendJob3 a b c (0,0,0) j).2.1 + (((1:ℕ):ℝ) + 1) * G,
         (appendJob3 a b c (0,0,0) j).2.2 + (((1:ℕ):ℝ) + 2) * G) := by
      simp only [appendJob3, Prod.mk.injEq]
      refine ⟨by push_cast; ring, ?_, ?_⟩ <;>
        (simp only [max_def]; split_ifs <;> push_cast <;> linarith)
    rw [this, my_foldl3_shift a b c G J _ 1]
    simp only [List.length_cons]
    have : 1 + J.length = J.length + 1 := by omega
    rw [this]

theorem my_card_unscheduled {n : ℕ} (J : List (Fin n)) (hJ : J.Nodup) :
    (IgnallSchrage.Makespan.unscheduled J).card = n - J.length := by
  have : IgnallSchrage.Makespan.unscheduled J = Finset.univ \ J.toFinset := by
    ext x; simp [IgnallSchrage.Makespan.unscheduled]
  rw [this, Finset.card_univ_sdiff, Fintype.card_fin, List.toFinset_card_of_nodup hJ]

theorem my_lowerBound3_shift {n : ℕ} (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (G : ℝ) (hG : 0 < G)
    (J : List (Fin n)) (hJ : J.Nodup) (hr1 : 1 ≤ J.length) (hrn : J.length + 1 ≤ n) :
    lowerBound3 (fun i => a i + G) (fun i => b i + G) (fun i => c i + G) J =
      lowerBound3 a b c J + G * (n + 2) := by
  have hcard := my_card_unscheduled J hJ
  have hne : (IgnallSchrage.Makespan.unscheduled J).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  have hc' : ((IgnallSchrage.Makespan.unscheduled J).card : ℝ) = (n : ℝ) - J.length := by
    rw [hcard, Nat.cast_sub (by omega)]
  simp only [lowerBound3]
  rw [my_times3_shift a b c ha hb hc G hG J hr1]
  have e1 : (fun i => (b i + G) + (c i + G)) = fun i => (b i + c i) + 2 * G := by funext i; ring
  rw [e1, my_minOver_add_const hne, my_minOver_add_const hne]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hc']
  simp only [max_def]
  split_ifs <;> linarith


open IgnallSchrage.Makespan in
def myGood (n : ℕ) (P : List (Fin n)) : Prop := P.Nodup ∧ 1 ≤ P.length ∧ P.length + 1 ≤ n

open IgnallSchrage.Makespan in
theorem my_mem_insertNode {n : ℕ} (LB : List (Fin n) → ℝ) (x : List (Fin n)) (L : List (List (Fin n)))
    (y : List (Fin n)) (hy : y ∈ insertNode LB x L) : y = x ∨ y ∈ L := by
  induction L with
  | nil => simp [insertNode] at hy; exact Or.inl hy
  | cons z zs ih =>
    unfold insertNode at hy
    split_ifs at hy with h
    · simp at hy; rcases hy with h | h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
      · exact Or.inr (by simp [h])
    · simp at hy; rcases hy with h | h
      · exact Or.inr (by simp [h])
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

open IgnallSchrage.Makespan in
theorem my_insert_congr {n : ℕ} (LB' LB : List (Fin n) → ℝ)
    (hrel : ∀ x y, myGood n x → myGood n y → (LB' x ≤ LB' y ↔ LB x ≤ LB y))
    (x : List (Fin n)) (hx : myGood n x) (L : List (List (Fin n))) (hL : ∀ y ∈ L, myGood n y) :
    insertNode LB' x L = insertNode LB x L := by
  induction L with
  | nil => rfl
  | cons z zs ih =>
    have hz := hL z (by simp)
    have hzs : ∀ y ∈ zs, myGood n y := fun y hy => hL y (by simp [hy])
    unfold insertNode
    rw [ih hzs]
    by_cases h : LB x ≤ LB z
    · rw [if_pos ((hrel x z hx hz).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hrel x z hx hz).1 h')), if_neg h]

open IgnallSchrage.Makespan in
theorem my_foldl_insert_mem {n : ℕ} (LB : List (Fin n) → ℝ) (cs : List (List (Fin n))) :
    ∀ (L : List (List (Fin n))) (y : List (Fin n)),
      y ∈ cs.foldl (fun L x => insertNode LB x L) L → y ∈ cs ∨ y ∈ L := by
  induction cs with
  | nil => intro L y hy; exact Or.inr hy
  | cons c cs ih =>
    intro L y hy
    simp only [List.foldl_cons] at hy
    rcases ih _ y hy with h | h
    · exact Or.inl (by simp [h])
    · rcases my_mem_insertNode LB c L y h with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr h

open IgnallSchrage.Makespan in
theorem my_foldl_insert_congr {n : ℕ} (LB' LB : List (Fin n) → ℝ)
    (hrel : ∀ x y, myGood n x → myGood n y → (LB' x ≤ LB' y ↔ LB x ≤ LB y))
    (cs : List (List (Fin n))) :
    ∀ (L : List (List (Fin n))), (∀ c ∈ cs, myGood n c) → (∀ y ∈ L, myGood n y) →
      cs.foldl (fun L x => insertNode LB' x L) L = cs.foldl (fun L x => insertNode LB x L) L := by
  induction cs with
  | nil => intro L _ _; rfl
  | cons c cs ih =>
    intro L hc hL
    simp only [List.foldl_cons]
    rw [my_insert_congr LB' LB hrel c (hc c (by simp)) L hL]
    apply ih
    · intro d hd; exact hc d (by simp [hd])
    · intro y hy
      rcases my_mem_insertNode LB c L y hy with h | h
      · rw [h]; exact hc c (by simp)
      · exact hL y h

open IgnallSchrage.Makespan in
theorem my_children_good {n : ℕ} (P : List (Fin n)) (hP : P.Nodup) (ht : ¬ IsTerminal P) :
    ∀ c ∈ children P, myGood n c := by
  intro c hc
  unfold children at hc
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have hnd : (P ++ [j]).Nodup := by
    refine List.nodup_append.2 ⟨hP, List.nodup_singleton j, ?_⟩
    intro a ha b hb hab; simp at hb; subst hb; subst hab; exact hj ha
  have hle := hnd.length_le_card
  simp only [List.length_append, List.length_singleton, Fintype.card_fin] at hle
  unfold IsTerminal at ht
  refine ⟨hnd, by simp, ?_⟩
  simp only [List.length_append, List.length_singleton]; omega

open IgnallSchrage.Makespan in
def myInv (n : ℕ) (L : List (List (Fin n))) : Prop := L = [[]] ∨ ∀ P ∈ L, myGood n P

open IgnallSchrage.Makespan in
theorem my_inv_cons {n : ℕ} (P : List (Fin n)) (rest : List (List (Fin n))) (h : myInv n (P :: rest)) :
    P.Nodup ∧ ∀ y ∈ rest, myGood n y := by
  rcases h with h | h
  · simp at h; obtain ⟨rfl, rfl⟩ := h; simp
  · exact ⟨(h P (by simp)).1, fun y hy => h y (by simp [hy])⟩

open IgnallSchrage.Makespan in
theorem my_step_inv {n : ℕ} (LB : List (Fin n) → ℝ) (L : List (List (Fin n))) (h : myInv n L) :
    myInv n (step LB L) := by
  cases L with
  | nil => right; simp [step]
  | cons P rest =>
    obtain ⟨hP, hrest⟩ := my_inv_cons P rest h
    simp only [step]
    by_cases ht : IsTerminal P
    · rw [if_pos ht]; exact h
    · rw [if_neg ht]
      right
      intro y hy
      rcases my_foldl_insert_mem LB _ rest y hy with h | h
      · exact my_children_good P hP ht y h
      · exact hrest y h

open IgnallSchrage.Makespan in
theorem my_step_congr {n : ℕ} (LB' LB : List (Fin n) → ℝ)
    (hrel : ∀ x y, myGood n x → myGood n y → (LB' x ≤ LB' y ↔ LB x ≤ LB y))
    (L : List (List (Fin n))) (h : myInv n L) : step LB' L = step LB L := by
  cases L with
  | nil => simp [step]
  | cons P rest =>
    obtain ⟨hP, hrest⟩ := my_inv_cons P rest h
    simp only [step]
    by_cases ht : IsTerminal P
    · rw [if_pos ht, if_pos ht]
    · rw [if_neg ht, if_neg ht]
      exact my_foldl_insert_congr LB' LB hrel _ rest (my_children_good P hP ht) hrest

open IgnallSchrage.Makespan in
theorem my_run_inv {n : ℕ} (LB : List (Fin n) → ℝ) (k : ℕ) : myInv n (run LB k) := by
  induction k with
  | zero => left; simp [run]
  | succ k ih =>
    unfold run at ih ⊢
    rw [Function.iterate_succ_apply']
    exact my_step_inv LB _ ih

theorem my_run_eq_of_strictMono {n : ℕ} (LB LB' : List (Fin n) → ℝ) (φ : ℝ → ℝ)
    (hφ : StrictMono φ)
    (h : ∀ J : List (Fin n), J.Nodup → 1 ≤ J.length → J.length + 1 ≤ n → LB' J = φ (LB J)) :
    ∀ k : ℕ, IgnallSchrage.Makespan.run LB' k = IgnallSchrage.Makespan.run LB k := by
  have hrel : ∀ x y, myGood n x → myGood n y → (LB' x ≤ LB' y ↔ LB x ≤ LB y) := by
    intro x y hx hy
    rw [h x hx.1 hx.2.1 hx.2.2, h y hy.1 hy.2.1 hy.2.2]
    exact hφ.le_iff_le
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : ∀ LB : List (Fin n) → ℝ, IgnallSchrage.Makespan.run LB (k+1) =
        IgnallSchrage.Makespan.step LB (IgnallSchrage.Makespan.run LB k) := by
      intro LB; unfold IgnallSchrage.Makespan.run; rw [Function.iterate_succ_apply']
    rw [e, e, ih]
    exact my_step_congr LB' LB hrel _ (my_run_inv LB k)


theorem my_appendJob2_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (t : ℝ × ℝ × ℝ) (i : Fin n) :
    appendJob2 (fun i => H * a i) (fun i => H * b i) (H * t.1, H * t.2.1, H * t.2.2) i =
      (H * (appendJob2 a b t i).1, H * (appendJob2 a b t i).2.1, H * (appendJob2 a b t i).2.2) := by
  simp only [appendJob2, Prod.mk.injEq]
  have e : max (H * t.2.1) (H * t.1 + H * a i) = H * max t.2.1 (t.1 + a i) := by
    rw [← mul_add, ← mul_max_of_nonneg _ _ hH.le]
  refine ⟨by ring, ?_, ?_⟩ <;> (rw [e]; ring)

theorem my_foldl2_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J : List (Fin n)) :
    ∀ t : ℝ × ℝ × ℝ,
    J.foldl (appendJob2 (fun i => H * a i) (fun i => H * b i)) (H * t.1, H * t.2.1, H * t.2.2) =
      (H * (J.foldl (appendJob2 a b) t).1, H * (J.foldl (appendJob2 a b) t).2.1,
        H * (J.foldl (appendJob2 a b) t).2.2) := by
  induction J with
  | nil => intro t; simp
  | cons j J ih =>
    intro t
    simp only [List.foldl_cons]
    rw [my_appendJob2_scale a b H hH t j]
    exact ih _

theorem my_state2_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J : List (Fin n)) :
    state2 (fun i => H * a i) (fun i => H * b i) J =
      (H * (state2 a b J).1, H * (state2 a b J).2.1, H * (state2 a b J).2.2) := by
  unfold state2
  have := my_foldl2_scale a b H hH J (0, 0, 0)
  simpa using this

theorem my_Tval_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J l : List (Fin n)) :
    Tval (fun i => H * a i) (fun i => H * b i) J l = H * Tval a b J l := by
  unfold Tval
  rw [my_state2_scale a b H hH J, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only; ring

theorem my_Sval_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J l : List (Fin n)) :
    Sval (fun i => H * a i) (fun i => H * b i) J l = H * Sval a b J l := by
  unfold Sval
  rw [my_state2_scale a b H hH J, my_minOver_mul_const _ _ _ hH, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only
  rw [← mul_add, ← mul_max_of_nonneg _ _ hH.le]; ring

theorem my_That_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J : List (Fin n)) :
    That (fun i => H * a i) (fun i => H * b i) J = H * That a b J := by
  unfold That
  rw [← my_inf'_mul_const _ _ H hH]
  exact Finset.inf'_congr _ rfl (fun l _ => my_Tval_scale a b H hH J l)

theorem my_Shat_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J : List (Fin n)) :
    Shat (fun i => H * a i) (fun i => H * b i) J = H * Shat a b J := by
  unfold Shat
  rw [← my_inf'_mul_const _ _ H hH]
  exact Finset.inf'_congr _ rfl (fun l _ => my_Sval_scale a b H hH J l)

theorem my_lowerBound2_scale {n : ℕ} (a b : Fin n → ℝ) (H : ℝ) (hH : 0 < H) (J : List (Fin n)) :
    lowerBound2 (fun i => H * a i) (fun i => H * b i) J = H * lowerBound2 a b J := by
  unfold lowerBound2
  rw [my_state2_scale a b H hH J, my_That_scale a b H hH, my_Shat_scale a b H hH,
    ← mul_max_of_nonneg _ _ hH.le]
  ring

theorem my_appendJob2_shift {n : ℕ} (a b : Fin n → ℝ) (G : ℝ) (t : ℝ × ℝ × ℝ) (s : ℕ) (j : Fin n) :
    appendJob2 (fun i => a i + G) (fun i => b i + G)
        (t.1 + s * G, t.2.1 + (s + 1) * G, t.2.2 + G * s * (s + 3) / 2) j =
      ((appendJob2 a b t j).1 + ((s + 1 : ℕ) : ℝ) * G,
       (appendJob2 a b t j).2.1 + (((s + 1 : ℕ) : ℝ) + 1) * G,
       (appendJob2 a b t j).2.2 + G * ((s + 1 : ℕ) : ℝ) * (((s + 1 : ℕ) : ℝ) + 3) / 2) := by
  simp only [appendJob2, Prod.mk.injEq]
  refine ⟨by push_cast; ring, ?_, ?_⟩
  · have : max (t.2.1 + (s + 1) * G) (t.1 + s * G + (a j + G)) =
        max t.2.1 (t.1 + a j) + ((s:ℝ) + 1) * G := by
      rw [← max_add_add_right]; congr 1; ring
    rw [this]; push_cast; ring
  · have : max (t.2.1 + (s + 1) * G) (t.1 + s * G + (a j + G)) =
        max t.2.1 (t.1 + a j) + ((s:ℝ) + 1) * G := by
      rw [← max_add_add_right]; congr 1; ring
    rw [this]; push_cast; ring

theorem my_foldl2_shift {n : ℕ} (a b : Fin n → ℝ) (G : ℝ) (J : List (Fin n)) :
    ∀ (t : ℝ × ℝ × ℝ) (s : ℕ),
    J.foldl (appendJob2 (fun i => a i + G) (fun i => b i + G))
        (t.1 + s * G, t.2.1 + (s + 1) * G, t.2.2 + G * s * (s + 3) / 2) =
      ((J.foldl (appendJob2 a b) t).1 + ((s + J.length : ℕ) : ℝ) * G,
       (J.foldl (appendJob2 a b) t).2.1 + (((s + J.length : ℕ) : ℝ) + 1) * G,
       (J.foldl (appendJob2 a b) t).2.2 +
         G * ((s + J.length : ℕ) : ℝ) * (((s + J.length : ℕ) : ℝ) + 3) / 2) := by
  induction J with
  | nil => intro t s; simp
  | cons j J ih =>
    intro t s
    simp only [List.foldl_cons]
    rw [my_appendJob2_shift a b G t s j, ih]
    simp only [List.length_cons]
    have : s + 1 + J.length = s + (J.length + 1) := by omega
    rw [this]

theorem my_state2_shift {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (J : List (Fin n)) (hJ : 1 ≤ J.length) :
    state2 (fun i => a i + G) (fun i => b i + G) J =
      ((state2 a b J).1 + (J.length : ℝ) * G,
       (state2 a b J).2.1 + ((J.length : ℝ) + 1) * G,
       (state2 a b J).2.2 + G * (J.length : ℝ) * ((J.length : ℝ) + 3) / 2) := by
  cases J with
  | nil => simp at hJ
  | cons j J =>
    unfold state2
    simp only [List.foldl_cons]
    have h1 := ha j; have h2 := hb j
    have : appendJob2 (fun i => a i + G) (fun i => b i + G) (0, 0, 0) j =
        ((appendJob2 a b (0,0,0) j).1 + ((1:ℕ):ℝ) * G,
         (appendJob2 a b (0,0,0) j).2.1 + (((1:ℕ):ℝ) + 1) * G,
         (appendJob2 a b (0,0,0) j).2.2 + G * ((1:ℕ):ℝ) * (((1:ℕ):ℝ) + 3) / 2) := by
      simp only [appendJob2, Prod.mk.injEq]
      refine ⟨by push_cast; ring, ?_, ?_⟩ <;>
        (simp only [max_def]; split_ifs <;> push_cast <;> linarith)
    rw [this, my_foldl2_shift a b G J _ 1]
    simp only [List.length_cons]
    have : 1 + J.length = J.length + 1 := by omega
    rw [this]

theorem my_sum_sub (L : ℕ) : ∑ p ∈ Finset.range L, (((L - p : ℕ)) : ℝ) = (L : ℝ) * ((L : ℝ) + 1) / 2 := by
  have : ∀ m, m ≤ L → ∑ p ∈ Finset.range m, (((L - p : ℕ)) : ℝ) =
      (m : ℝ) * L - (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ, ih (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
  rw [this L le_rfl]; ring

theorem my_orderings_length {n : ℕ} (J l : List (Fin n)) (hl : l ∈ orderings J) :
    l.length = n - J.length ∨ True := Or.inr trivial

theorem my_orderings_length' {n : ℕ} (J l : List (Fin n)) (hJ : J.Nodup) (hl : l ∈ orderings J) :
    l.length = n - J.length := by
  unfold orderings at hl
  rw [List.mem_toFinset, List.mem_permutations] at hl
  rw [hl.length_eq, Finset.length_toList, my_card_unscheduled J hJ]

theorem my_Tval_shift {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (J : List (Fin n)) (hr1 : 1 ≤ J.length) (l : List (Fin n)) :
    Tval (fun i => a i + G) (fun i => b i + G) J l =
      Tval a b J l + G * ((J.length : ℝ) * (l.length : ℝ) +
        (l.length : ℝ) * ((l.length : ℝ) + 1) / 2 + (l.length : ℝ)) := by
  unfold Tval
  have hs := my_state2_shift a b ha hb G hG J hr1
  have : ∀ p : Fin l.length,
      ((state2 (fun i => a i + G) (fun i => b i + G) J).1 +
        ((l.length - p.val : ℕ) : ℝ) * (a l[p] + G) + (b l[p] + G)) =
      ((state2 a b J).1 + ((l.length - p.val : ℕ) : ℝ) * a l[p] + b l[p]) +
        (J.length * G + ((l.length - p.val : ℕ) : ℝ) * G + G) := by
    intro p; rw [hs]; simp only; ring
  rw [Finset.sum_congr rfl (fun p _ => this p), Finset.sum_add_distrib]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun p => (J.length : ℝ) * G + ((l.length - p : ℕ) : ℝ) * G + G) l.length]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, my_sum_sub, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

theorem my_Sval_shift {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (J : List (Fin n)) (hJ : J.Nodup) (hr1 : 1 ≤ J.length) (hrn : J.length + 1 ≤ n) (l : List (Fin n)) :
    Sval (fun i => a i + G) (fun i => b i + G) J l =
      Sval a b J l + G * ((J.length : ℝ) * (l.length : ℝ) +
        (l.length : ℝ) * ((l.length : ℝ) + 1) / 2 + (l.length : ℝ)) := by
  have hcard := my_card_unscheduled J hJ
  have hne : (IgnallSchrage.Makespan.unscheduled J).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  unfold Sval
  have hs := my_state2_shift a b ha hb G hG J hr1
  have hm := my_minOver_add_const hne a G
  have : ∀ p : Fin l.length,
      (max (state2 (fun i => a i + G) (fun i => b i + G) J).2.1
        ((state2 (fun i => a i + G) (fun i => b i + G) J).1 +
          IgnallSchrage.Makespan.minOver (IgnallSchrage.Makespan.unscheduled J) (fun i => a i + G)) +
        ((l.length - p.val : ℕ) : ℝ) * (b l[p] + G)) =
      (max (state2 a b J).2.1 ((state2 a b J).1 +
          IgnallSchrage.Makespan.minOver (IgnallSchrage.Makespan.unscheduled J) a) +
        ((l.length - p.val : ℕ) : ℝ) * b l[p]) +
        ((J.length + 1) * G + ((l.length - p.val : ℕ) : ℝ) * G) := by
    intro p
    rw [hs, hm]
    simp only
    have : max ((state2 a b J).2.1 + ((J.length : ℝ) + 1) * G)
        ((state2 a b J).1 + J.length * G +
          (IgnallSchrage.Makespan.minOver (IgnallSchrage.Makespan.unscheduled J) a + G)) =
        max (state2 a b J).2.1 ((state2 a b J).1 +
          IgnallSchrage.Makespan.minOver (IgnallSchrage.Makespan.unscheduled J) a) +
          ((J.length : ℝ) + 1) * G := by
      rw [← max_add_add_right]; congr 1; ring
    rw [this]; ring
  rw [Finset.sum_congr rfl (fun p _ => this p), Finset.sum_add_distrib]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun p => ((J.length : ℝ) + 1) * G + ((l.length - p : ℕ) : ℝ) * G) l.length]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, my_sum_sub, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

theorem my_lowerBound2_shift {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (J : List (Fin n)) (hJ : J.Nodup) (hr1 : 1 ≤ J.length) (hrn : J.length + 1 ≤ n) :
    That (fun i => a i + G) (fun i => b i + G) J =
      That a b J + G * ((J.length : ℝ) * ((n : ℝ) - J.length) +
        ((n : ℝ) - J.length) * ((n : ℝ) - J.length + 1) / 2 + ((n : ℝ) - J.length)) ∧
    Shat (fun i => a i + G) (fun i => b i + G) J =
      Shat a b J + G * ((J.length : ℝ) * ((n : ℝ) - J.length) +
        ((n : ℝ) - J.length) * ((n : ℝ) - J.length + 1) / 2 + ((n : ℝ) - J.length)) ∧
    (state2 (fun i => a i + G) (fun i => b i + G) J).2.2 =
      (state2 a b J).2.2 + G * (J.length : ℝ) * ((J.length : ℝ) + 3) / 2 ∧
    lowerBound2 (fun i => a i + G) (fun i => b i + G) J =
      lowerBound2 a b J + G * n * (n + 3) / 2 := by
  have hT : That (fun i => a i + G) (fun i => b i + G) J =
      That a b J + G * ((J.length : ℝ) * ((n : ℝ) - J.length) +
        ((n : ℝ) - J.length) * ((n : ℝ) - J.length + 1) / 2 + ((n : ℝ) - J.length)) := by
    unfold That
    rw [← my_inf'_add_const]
    refine Finset.inf'_congr _ rfl (fun l hl => ?_)
    rw [my_Tval_shift a b ha hb G hG J hr1 l, my_orderings_length' J l hJ hl, Nat.cast_sub (by omega)]
  have hS : Shat (fun i => a i + G) (fun i => b i + G) J =
      Shat a b J + G * ((J.length : ℝ) * ((n : ℝ) - J.length) +
        ((n : ℝ) - J.length) * ((n : ℝ) - J.length + 1) / 2 + ((n : ℝ) - J.length)) := by
    unfold Shat
    rw [← my_inf'_add_const]
    refine Finset.inf'_congr _ rfl (fun l hl => ?_)
    rw [my_Sval_shift a b ha hb G hG J hJ hr1 hrn l, my_orderings_length' J l hJ hl,
      Nat.cast_sub (by omega)]
  have hD := (my_state2_shift a b ha hb G hG J hr1)
  refine ⟨hT, hS, by rw [hD], ?_⟩
  unfold lowerBound2
  rw [hT, hS, hD]
  simp only
  rw [max_add_add_right]
  ring


theorem my_scale_core {n : ℕ} (a b c : Fin n → ℝ) (H : ℝ) (hH : 0 < H) :
    (∀ σ : Equiv.Perm (Fin n),
      IgnallSchrage.Makespan.makespan (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) σ =
        H * IgnallSchrage.Makespan.makespan a b c σ) ∧
    (∀ σ : Equiv.Perm (Fin n),
      sumCompletion (fun i => H * a i) (fun i => H * b i) σ = H * sumCompletion a b σ) ∧
    (∀ J : List (Fin n),
      lowerBound3 (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) J =
        H * lowerBound3 a b c J) ∧
    (∀ J : List (Fin n),
      That (fun i => H * a i) (fun i => H * b i) J = H * That a b J ∧
      Shat (fun i => H * a i) (fun i => H * b i) J = H * Shat a b J ∧
      lowerBound2 (fun i => H * a i) (fun i => H * b i) J = H * lowerBound2 a b J) :=
  ⟨fun σ => my_makespan_scale a b c H hH σ, fun σ => my_sumCompletion_scale a b H hH σ,
    fun J => my_lowerBound3_scale a b c H hH J,
    fun J => ⟨my_That_scale a b H hH J, my_Shat_scale a b H hH J, my_lowerBound2_scale a b H hH J⟩⟩

theorem my_completion_shift_core {n : ℕ} (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) (r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    JohnsonFlowShop.ThreeStage.asapDone (fun i => a i + G) (fun i => b i + G)
        (fun i => c i + G) σ r =
      ((JohnsonFlowShop.ThreeStage.asapDone a b c σ r).1 + r * G,
       (JohnsonFlowShop.ThreeStage.asapDone a b c σ r).2.1 + (r + 1) * G,
       (JohnsonFlowShop.ThreeStage.asapDone a b c σ r).2.2 + (r + 2) * G) ∧
    JohnsonFlowShop.TwoStage.asapC2 (fun i => a i + G) (fun i => b i + G) σ r =
      JohnsonFlowShop.TwoStage.asapC2 a b σ r + (r + 1) * G :=
  ⟨my_asapDone_shift a b c ha hb hc G hG σ r hr1 hrn, my_asapC2_shift a b ha hb G hG σ r hr1 hrn⟩

theorem my_opt_iff {ι : Type*} (f g : ι → ℝ) (φ : ℝ → ℝ) (hφ : StrictMono φ)
    (h : ∀ σ, f σ = φ (g σ)) (σ : ι) :
    (∀ τ, f σ ≤ f τ) ↔ (∀ τ, g σ ≤ g τ) := by
  simp only [h, hφ.le_iff_le]

theorem my_location_scale_core {n : ℕ} (a' b' c' : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a' i) (hb : ∀ i, 0 ≤ b' i) (hc : ∀ i, 0 ≤ c' i) (H G : ℝ)
    (hH : 0 < H) (hG : 0 < G) :
    (∀ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        IgnallSchrage.Makespan.makespan (shiftScale H G a') (shiftScale H G b') (shiftScale H G c') σ ≤
          IgnallSchrage.Makespan.makespan (shiftScale H G a') (shiftScale H G b') (shiftScale H G c') τ) ↔
      (∀ τ : Equiv.Perm (Fin n), IgnallSchrage.Makespan.makespan a' b' c' σ ≤ IgnallSchrage.Makespan.makespan a' b' c' τ)) ∧
    (∀ k : ℕ,
      IgnallSchrage.Makespan.run (lowerBound3 (shiftScale H G a') (shiftScale H G b') (shiftScale H G c')) k =
        IgnallSchrage.Makespan.run (lowerBound3 a' b' c') k) ∧
    (∀ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        sumCompletion (shiftScale H G a') (shiftScale H G b') σ ≤
          sumCompletion (shiftScale H G a') (shiftScale H G b') τ) ↔
      (∀ τ : Equiv.Perm (Fin n), sumCompletion a' b' σ ≤ sumCompletion a' b' τ)) ∧
    (∀ k : ℕ,
      IgnallSchrage.Makespan.run (lowerBound2 (shiftScale H G a') (shiftScale H G b')) k =
        IgnallSchrage.Makespan.run (lowerBound2 a' b') k) := by
  have hφ : ∀ K : ℝ, StrictMono (fun x : ℝ => H * (x + K)) := by
    intro K x y hxy
    simp only
    exact mul_lt_mul_of_pos_left (by linarith) hH
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      constructor <;> intro _ τ <;> rw [Subsingleton.elim τ σ]
    · refine my_opt_iff _ _ (fun x => H * (x + G * (n + 2))) (hφ _) ?_ σ
      intro σ
      have := my_makespan_scale (fun i => a' i + G) (fun i => b' i + G) (fun i => c' i + G) H hH σ
      rw [my_makespan_shift hn a' b' c' ha hb hc G hG σ] at this
      exact this
  · intro k
    refine my_run_eq_of_strictMono (lowerBound3 a' b' c') _ (fun x => H * (x + G * (n + 2))) (hφ _) ?_ k
    intro J hJ hr1 hrn
    have := my_lowerBound3_scale (fun i => a' i + G) (fun i => b' i + G) (fun i => c' i + G) H hH J
    rw [my_lowerBound3_shift a' b' c' ha hb hc G hG J hJ hr1 hrn] at this
    exact this
  · intro σ
    refine my_opt_iff _ _ (fun x => H * (x + G * n * (n + 3) / 2)) (hφ _) ?_ σ
    intro σ
    have := my_sumCompletion_scale (fun i => a' i + G) (fun i => b' i + G) H hH σ
    rw [my_sumCompletion_shift a' b' ha hb G hG σ] at this
    exact this
  · intro k
    refine my_run_eq_of_strictMono (lowerBound2 a' b') _ (fun x => H * (x + G * n * (n + 3) / 2)) (hφ _) ?_ k
    intro J hJ hr1 hrn
    have := my_lowerBound2_scale (fun i => a' i + G) (fun i => b' i + G) H hH J
    rw [(my_lowerBound2_shift a' b' ha hb G hG J hJ hr1 hrn).2.2.2] at this
    exact this

end IgnallSchrage.Invariance

open IgnallSchrage.Invariance


theorem solution {n : ℕ} (a' b' c' : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a' i) (hb : ∀ i, 0 ≤ b' i) (hc : ∀ i, 0 ≤ c' i) (H G : ℝ)
    (hH : 0 < H) (hG : 0 < G) :
    (∀ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        IgnallSchrage.Makespan.makespan (shiftScale H G a') (shiftScale H G b') (shiftScale H G c') σ ≤
          IgnallSchrage.Makespan.makespan (shiftScale H G a') (shiftScale H G b') (shiftScale H G c') τ) ↔
      (∀ τ : Equiv.Perm (Fin n), IgnallSchrage.Makespan.makespan a' b' c' σ ≤ IgnallSchrage.Makespan.makespan a' b' c' τ)) ∧
    (∀ k : ℕ,
      IgnallSchrage.Makespan.run (lowerBound3 (shiftScale H G a') (shiftScale H G b') (shiftScale H G c')) k =
        IgnallSchrage.Makespan.run (lowerBound3 a' b' c') k) ∧
    (∀ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        sumCompletion (shiftScale H G a') (shiftScale H G b') σ ≤
          sumCompletion (shiftScale H G a') (shiftScale H G b') τ) ↔
      (∀ τ : Equiv.Perm (Fin n), sumCompletion a' b' σ ≤ sumCompletion a' b' τ)) ∧
    (∀ k : ℕ,
      IgnallSchrage.Makespan.run (lowerBound2 (shiftScale H G a') (shiftScale H G b')) k =
        IgnallSchrage.Makespan.run (lowerBound2 a' b') k) := by
  exact my_location_scale_core a' b' c' ha hb hc H G hH hG
