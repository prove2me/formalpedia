-- Prove2me | solution 1 for HassinRSP.Rounding.rounding_error
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:57:10.847334+00:00
-- url     : https://prove2.me/submissions/989a1530-19c3-4c47-ba63-dc5252249690

import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting



namespace HassinRSP.Rounding

lemma e3_edges_mem (F : Finset (ℕ × ℕ)) (p : List ℕ)
    (h : p.IsChain (fun a b => (a, b) ∈ F)) : ∀ e ∈ p.zip p.tail, e ∈ F := by
  induction p with
  | nil => simp
  | cons a rest ih =>
    cases rest with
    | nil => simp
    | cons b r =>
      rw [List.isChain_cons_cons] at h
      intro e he
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact h.1
      · exact ih h.2 e (by simpa using he)

lemma e3_len (I : Instance) (hI : I.WellFormed) : ∀ (rest : List ℕ) (a : ℕ),
    (a :: rest).IsChain (fun a b => (a, b) ∈ I.E) → rest = [] ∨ (1 ≤ a ∧ rest.length + a ≤ I.n) := by
  intro rest
  induction rest with
  | nil => intro a _; left; rfl
  | cons b r ih =>
    intro a h
    rw [List.isChain_cons_cons] at h
    have hE := hI.2.1 (a, b) h.1
    simp only at hE
    right
    refine ⟨hE.1, ?_⟩
    rcases ih b h.2 with hr | hr
    · subst hr; simp; omega
    · simp only [List.length_cons]; omega

lemma e3_count (I : Instance) (hI : I.WellFormed) (i j : ℕ) (p : List ℕ) (hp : IsPathIn I.E i j p) :
    (p.zip p.tail).length ≤ I.n - 1 := by
  obtain ⟨_, _, hc⟩ := hp
  cases p with
  | nil => simp
  | cons a rest =>
    rcases e3_len I hI rest a hc with h | h
    · subst h; simp
    · simp [List.length_zip]; omega

lemma e3_delta (I : Instance) (hI : I.WellFormed) (ε V : ℝ) (hε : 0 < ε) (hV : 0 < V) :
    0 < V * ε / ((I.n : ℝ) - 1) := by
  have : (2:ℝ) ≤ I.n := by exact_mod_cast hI.1
  apply div_pos (mul_pos hV hε); linarith

lemma e3_edge (I : Instance) (hI : I.WellFormed) (ε : ℝ) (hε : 0 < ε) (V : ℝ) (hV : 0 < V) (e : ℕ × ℕ) :
    V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ I.c e ∧
      (I.c e : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ V * ε / ((I.n : ℝ) - 1) := by
  have hδ := e3_delta I hI ε V hε hV
  have hn : (2:ℝ) ≤ I.n := by exact_mod_cast hI.1
  have hx : (I.c e : ℝ) * ((I.n : ℝ) - 1) / (V * ε) = I.c e / (V * ε / ((I.n : ℝ) - 1)) := by
    have : (I.n : ℝ) - 1 ≠ 0 := by linarith
    have : V * ε ≠ 0 := by positivity
    field_simp
  unfold roundLen
  rw [hx]
  set δ := V * ε / ((I.n : ℝ) - 1)
  have h1 := Nat.floor_le (div_nonneg (Nat.cast_nonneg (I.c e)) hδ.le)
  have h2 := Nat.lt_floor_add_one ((I.c e : ℝ) / δ)
  rw [le_div_iff₀ hδ] at h1
  rw [div_lt_iff₀ hδ] at h2
  constructor <;> nlinarith

lemma e3_sum (I : Instance) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ e, δ * roundLen I 1 1 e ≤ 0 → True) : True := trivial

lemma e3_list (c : ℕ × ℕ → ℕ) (r : ℕ × ℕ → ℕ) (δ : ℝ)
    (h : ∀ e, δ * (r e : ℝ) ≤ c e ∧ (c e : ℝ) - δ * r e ≤ δ) (S : List (ℕ × ℕ)) :
    δ * ((S.map r).sum : ℕ) ≤ ((S.map c).sum : ℕ) ∧
      (((S.map c).sum : ℕ) : ℝ) - δ * ((S.map r).sum : ℕ) ≤ S.length * δ := by
  induction S with
  | nil => simp
  | cons e S ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    simp only [Nat.cast_add, Nat.cast_succ]
    have := h e
    constructor <;> nlinarith [ih.1, ih.2]

lemma e3_path (I : Instance) (hI : I.WellFormed) (ε : ℝ) (hε : 0 < ε) (V : ℝ) (hV : 0 < V)
    (i j : ℕ) (p : List ℕ) (hp : IsPathIn I.E i j p) :
    V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ pathLen I p ∧
      (pathLen I p : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ V * ε := by
  have hn : (2:ℝ) ≤ I.n := by exact_mod_cast hI.1
  have hδ := e3_delta I hI ε V hε hV
  have L := e3_list I.c (roundLen I ε V) _ (fun e => e3_edge I hI ε hε V hV e) (p.zip p.tail)
  have hc := e3_count I hI i j p hp
  have hc' : ((p.zip p.tail).length : ℝ) ≤ (I.n : ℝ) - 1 := by
    have : ((p.zip p.tail).length : ℝ) ≤ ((I.n - 1 : ℕ) : ℝ) := by exact_mod_cast hc
    have h2 := hI.1
    rw [Nat.cast_sub (by omega)] at this; simpa using this
  have hVe : V * ε / ((I.n : ℝ) - 1) * ((I.n : ℝ) - 1) = V * ε := by
    have : (I.n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  unfold roundPathLen pathLen
  refine ⟨L.1, ?_⟩
  have := mul_le_mul_of_nonneg_left hc' hδ.le
  nlinarith [L.2]

theorem e3_rounding_error (I : Instance) (hI : I.WellFormed) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) (hV : 0 < V) :
    (∀ e ∈ I.E, V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ I.c e ∧
      (I.c e : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ V * ε / ((I.n : ℝ) - 1)) ∧
    (∀ (i j : ℕ) (p : List ℕ), IsPathIn I.E i j p →
      V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ pathLen I p ∧
      (pathLen I p : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ V * ε) :=
  ⟨fun e _ => e3_edge I hI ε hε0 V hV e, fun i j p hp => e3_path I hI ε hε0 V hV i j p hp⟩

lemma e3_pruned_sub (I : Instance) (V : ℝ) : prunedE I V ⊆ I.E := Finset.filter_subset _ _

lemma e3_path_mono {F G : Finset (ℕ × ℕ)} (h : F ⊆ G) {i j : ℕ} {p : List ℕ}
    (hp : IsPathIn F i j p) : IsPathIn G i j p := by
  refine ⟨hp.1, hp.2.1, ?_⟩
  have := e3_edges_mem F p hp.2.2
  refine List.IsChain.imp ?_ hp.2.2
  exact fun a b hab => h hab

theorem e3_test_no_spec (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) :
    testNo I T ε V → ∃ q, IsTPath I T q ∧ (pathLen I q : ℝ) < V * (1 + ε) := by
  rintro ⟨c, hc, p, hp, hT, hR⟩
  have hn : (2:ℝ) ≤ I.n := by exact_mod_cast hI.1
  have hV : 0 < V := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨h1, h2, h3⟩ := hp
    cases p with
    | nil => simp at h1
    | cons a rest =>
      cases rest with
      | nil =>
        simp at h1 h2; subst h1; have := hI.1; omega
      | cons b r =>
        rw [List.isChain_cons_cons] at h3
        have hm := h3.1
        simp only [prunedE, Finset.mem_filter] at hm
        have := hI.2.2 (a, b) hm.1
        have h0 : (0:ℝ) < I.c (a, b) := by exact_mod_cast this.1
        linarith [hm.2]
  have hp' : IsPathIn I.E 1 I.n p := e3_path_mono (e3_pruned_sub I V) hp
  refine ⟨p, ⟨hp', hT⟩, ?_⟩
  have hE := (e3_path I hI ε hε0 V hV 1 I.n p hp').2
  have hRc : (roundPathLen I ε V p : ℝ) ≤ c := by exact_mod_cast hR
  have hδ := e3_delta I hI ε V hε0 hV
  have h1 : V * ε / ((I.n : ℝ) - 1) * c < V * ε / ((I.n : ℝ) - 1) * (((I.n : ℝ) - 1) / ε) :=
    mul_lt_mul_of_pos_left hc hδ
  have h2 : V * ε / ((I.n : ℝ) - 1) * (((I.n : ℝ) - 1) / ε) = V := by
    have : (I.n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  have h3 := mul_le_mul_of_nonneg_left hRc hδ.le
  nlinarith

theorem e3_test_yes_spec (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) :
    testYes I T ε V → ∀ q, IsTPath I T q → V ≤ pathLen I q := by
  intro hy q hq
  by_contra hlt
  push_neg at hlt
  apply hy
  have hn : (2:ℝ) ≤ I.n := by exact_mod_cast hI.1
  have hV : 0 < V := lt_of_le_of_lt (Nat.cast_nonneg _) hlt
  obtain ⟨hq1, hqT⟩ := hq
  have hmem := e3_edges_mem I.E q hq1.2.2
  have hq2 : IsPathIn (prunedE I V) 1 I.n q := by
    refine ⟨hq1.1, hq1.2.1, ?_⟩
    have key : ∀ (l : List ℕ), l.IsChain (fun a b => (a, b) ∈ I.E) →
        (∀ e ∈ l.zip l.tail, (I.c e : ℝ) ≤ pathLen I q) → l.IsChain (fun a b => (a, b) ∈ prunedE I V) := by
      intro l
      induction l with
      | nil => intro _ _; exact List.isChain_nil
      | cons a rest ih =>
        cases rest with
        | nil => intro _ _; exact List.isChain_singleton _
        | cons b r =>
          intro h1 h2
          rw [List.isChain_cons_cons] at h1 ⊢
          refine ⟨?_, ih h1.2 ?_⟩
          · simp only [prunedE, Finset.mem_filter]
            refine ⟨h1.1, ?_⟩
            have := h2 (a, b) (by simp)
            linarith
          · intro e he
            exact h2 e (by simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at he ⊢; right; exact he)
    refine key q hq1.2.2 ?_
    intro e he
    have : I.c e ≤ pathLen I q := by
      unfold pathLen
      exact List.single_le_sum (fun x hx => Nat.zero_le x) _ (List.mem_map_of_mem he)
    exact_mod_cast this
  refine ⟨roundPathLen I ε V q, ?_, q, hq2, hqT, le_rfl⟩
  have hE := (e3_path I hI ε hε0 V hV 1 I.n q hq1).1
  have hδ := e3_delta I hI ε V hε0 hV
  have h2 : V * ε / ((I.n : ℝ) - 1) * (((I.n : ℝ) - 1) / ε) = V := by
    have : (I.n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  have : V * ε / ((I.n : ℝ) - 1) * (roundPathLen I ε V q : ℝ) < V * ε / ((I.n : ℝ) - 1) * (((I.n : ℝ) - 1) / ε) := by
    rw [h2]; linarith
  exact lt_of_mul_lt_mul_left this hδ.le

theorem e3_scaled_opt_error (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (LB : ℝ) (hLB : 0 < LB) (p : List ℕ) (hp : IsRoundingOutput I T ε LB p) :
    ∀ q, IsTPath I T q → (pathLen I p : ℝ) ≤ pathLen I q + ε * LB := by
  intro q hq
  have hn : (2:ℝ) ≤ I.n := by exact_mod_cast hI.1
  have h1 := (e3_path I hI ε hε0 LB hLB 1 I.n p hp.1.1).2
  have h2 := (e3_path I hI ε hε0 LB hLB 1 I.n q hq.1).1
  have hR : (roundPathLen I ε LB p : ℝ) ≤ roundPathLen I ε LB q := by exact_mod_cast hp.2 q hq
  have hδ := e3_delta I hI ε LB hε0 hLB
  have := mul_le_mul_of_nonneg_left hR hδ.le
  nlinarith

theorem e3_rounding_run_bounds (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (LB0 UB0 : ℝ) (hLB0 : 0 < LB0)
    (hLB0_le : ∀ q, IsTPath I T q → LB0 ≤ pathLen I q) (k : ℕ) :
    0 < (roundingRun I T ε LB0 UB0 k).1 ∧
    (∀ q, IsTPath I T q → (roundingRun I T ε LB0 UB0 k).1 ≤ pathLen I q) ∧
    ((∃ q, IsTPath I T q ∧ (pathLen I q : ℝ) ≤ UB0) →
      ∃ q, IsTPath I T q ∧ (pathLen I q : ℝ) ≤ (roundingRun I T ε LB0 UB0 k).2) := by
  induction k with
  | zero => exact ⟨hLB0, hLB0_le, id⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hr : roundingRun I T ε LB0 UB0 (k+1) = roundingStep I T ε (roundingRun I T ε LB0 UB0 k) := by
      unfold roundingRun; rw [Function.iterate_succ_apply']
    rw [hr]
    generalize roundingRun I T ε LB0 UB0 k = b at h1 h2 h3
    unfold roundingStep
    by_cases hb : b.2 ≤ 2 * b.1
    · simp only [hb, if_true]; exact ⟨h1, h2, h3⟩
    · simp only [hb, if_false]
      push_neg at hb
      have hUB : 0 < b.2 := by linarith
      have hs : 0 < Real.sqrt (b.1 * b.2) := Real.sqrt_pos.mpr (mul_pos h1 hUB)
      by_cases hy : testYes I T ε (Real.sqrt (b.1 * b.2))
      · simp only [hy, if_true]
        exact ⟨hs, e3_test_yes_spec I hI T ε hε0 _ hy, h3⟩
      · simp only [hy, if_false]
        refine ⟨h1, h2, fun hex => ?_⟩
        have hno : testNo I T ε (Real.sqrt (b.1 * b.2)) := by
          by_contra hn; exact hy hn
        obtain ⟨q, hq, hql⟩ := e3_test_no_spec I hI T ε hε0 _ hno
        exact ⟨q, hq, by nlinarith⟩

theorem e3_rounding_algorithm_approx (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (LB0 UB0 : ℝ) (hLB0 : 0 < LB0)
    (hLB0_le : ∀ q, IsTPath I T q → LB0 ≤ pathLen I q) (N : ℕ)
    (hstop : (roundingRun I T ε LB0 UB0 N).2 ≤ 2 * (roundingRun I T ε LB0 UB0 N).1)
    (p : List ℕ) (hp : IsRoundingOutput I T ε (roundingRun I T ε LB0 UB0 N).1 p) :
    ∀ q, IsTPath I T q → (pathLen I p : ℝ) ≤ (1 + ε) * pathLen I q := by
  intro q hq
  obtain ⟨h1, h2, _⟩ := e3_rounding_run_bounds I hI T ε hε0 LB0 UB0 hLB0 hLB0_le N
  have := e3_scaled_opt_error I hI T ε hε0 _ h1 p hp q hq
  have := h2 q hq
  nlinarith

end HassinRSP.Rounding

open HassinRSP.Rounding


theorem solution (I : Instance) (hI : I.WellFormed) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) (hV : 0 < V) :
    (∀ e ∈ I.E, V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ I.c e ∧
      (I.c e : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ V * ε / ((I.n : ℝ) - 1)) ∧
    (∀ (i j : ℕ) (p : List ℕ), IsPathIn I.E i j p →
      V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ pathLen I p ∧
      (pathLen I p : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ V * ε) := by
  exact e3_rounding_error I hI ε hε0 V hV
