-- Prove2me | solution 2 for HassinRSP.Rounding.rounding_algorithm_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:04:23.11681+00:00
-- url     : https://prove2.me/submissions/5cab26e3-15c1-443c-b22b-111c7a7050e6

import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting
import Theorems.Thm_HassinRSP_Rounding_rounding_run_bounds

-- carved verbatim out of submission 283a1b2d-c3fa-4555-803d-27fc47fe7dab, lines 268-275

section
open HassinRSP
open HassinRSP.Rounding

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

theorem e3_rounding_algorithm_approx (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (LB0 UB0 : ℝ) (hLB0 : 0 < LB0)
    (hLB0_le : ∀ q, IsTPath I T q → LB0 ≤ pathLen I q) (N : ℕ)
    (hstop : (roundingRun I T ε LB0 UB0 N).2 ≤ 2 * (roundingRun I T ε LB0 UB0 N).1)
    (p : List ℕ) (hp : IsRoundingOutput I T ε (roundingRun I T ε LB0 UB0 N).1 p) :
    ∀ q, IsTPath I T q → (pathLen I p : ℝ) ≤ (1 + ε) * pathLen I q := by
  intro q hq
  obtain ⟨h1, h2, _⟩ := HassinRSP.Rounding.rounding_run_bounds I hI T ε hε0 LB0 UB0 hLB0 hLB0_le N
  have := e3_scaled_opt_error I hI T ε hε0 _ h1 p hp q hq
  have := h2 q hq
  nlinarith

end

section
open HassinRSP.Rounding

theorem solution (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (LB0 UB0 : ℝ) (hLB0 : 0 < LB0)
    (hLB0_le : ∀ q, IsTPath I T q → LB0 ≤ pathLen I q) (N : ℕ)
    (hstop : (roundingRun I T ε LB0 UB0 N).2 ≤ 2 * (roundingRun I T ε LB0 UB0 N).1)
    (p : List ℕ) (hp : IsRoundingOutput I T ε (roundingRun I T ε LB0 UB0 N).1 p) :
    ∀ q, IsTPath I T q → (pathLen I p : ℝ) ≤ (1 + ε) * pathLen I q := by
  exact e3_rounding_algorithm_approx I hI T ε hε0 hε1 LB0 UB0 hLB0 hLB0_le N hstop p hp

end
