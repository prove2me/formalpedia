-- Prove2me | solution 1 for HolonomicPositivity.Robust.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:51:30.631127+00:00
-- url     : https://prove2.me/submissions/cb16df16-c1df-46d1-b214-8b1b758b8237

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Recurrence
import Definitions.Def_HolonomicPositivity_Robust_Conditions
import Theorems.Thm_HolonomicPositivity_Robust_lemma_5_1

section
set_option autoImplicit false
namespace HolonomicPositivity.Dev.T31
open HolonomicPositivity.Robust

noncomputable abbrev sf (P Q : RatFunc ℝ) (x : ℝ × ℝ × ℝ) (n : ℕ) : ℝ :=
  solutionFrom P Q x.1 x.2.1 x.2.2 n

theorem isSolution_from (P Q : RatFunc ℝ) (a b c : ℝ) : IsSolution P Q (solutionFrom P Q a b c) :=
  fun n => by rw [solutionFrom]

theorem sol_eq (P Q : RatFunc ℝ) (g : ℕ → ℝ) (hg : IsSolution P Q g) :
    g = solutionFrom P Q (g 0) (g 1) (g 2) :=
  (existsUnique_isSolution P Q (g 0) (g 1) (g 2)).unique ⟨hg, rfl, rfl, rfl⟩
    ⟨isSolution_from P Q _ _ _, rfl, rfl, rfl⟩

theorem sf_cont (P Q : RatFunc ℝ) (n : ℕ) :
    Continuous (fun x => sf P Q x n) ∧ Continuous (fun x => sf P Q x (n + 1)) ∧
      Continuous (fun x => sf P Q x (n + 2)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · exact continuous_fst
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    have : (fun x => sf P Q x (n + 1 + 2)) =
        fun x => sf P Q x (n + 2) + ev P n * sf P Q x (n + 1) + ev Q n * sf P Q x n := by
      funext x
      exact isSolution_from P Q _ _ _ n
    rw [this]
    exact (h2.add (continuous_const.mul h1)).add (continuous_const.mul h0)

theorem sf_surj (P Q : RatFunc ℝ) (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (N : ℕ) (y : ℝ × ℝ × ℝ) :
    ∃ x : ℝ × ℝ × ℝ, (sf P Q x N, sf P Q x (N + 1), sf P Q x (N + 2)) = y := by
  induction N generalizing y with
  | zero => exact ⟨y, rfl⟩
  | succ N ih =>
    obtain ⟨y0, y1, y2⟩ := y
    obtain ⟨x, hx⟩ := ih ((y2 - y1 - ev P N * y0) / ev Q N, y0, y1)
    simp only [Prod.mk.injEq] at hx
    obtain ⟨e0, e1, e2⟩ := hx
    refine ⟨x, ?_⟩
    have h3 : sf P Q x (N + 3) = sf P Q x (N + 2) + ev P N * sf P Q x (N + 1) + ev Q N * sf P Q x N :=
      isSolution_from P Q _ _ _ N
    have hq := hQ0 N
    simp only [Prod.mk.injEq]
    refine ⟨e1, e2, ?_⟩
    show sf P Q x (N + 3) = y2
    rw [h3, e0, e1, e2]
    field_simp
    ring

theorem exists_robust (P Q : RatFunc ℝ) (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (N : ℕ)
    (U : Set (ℝ × ℝ × ℝ)) (hU : IsOpen U) (y : ℝ × ℝ × ℝ) (hy : y ∈ U) :
    ∃ f : ℕ → ℝ, IsSolution P Q f ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ g : ℕ → ℝ, IsSolution P Q g →
        |g 0 - f 0| < ε → |g 1 - f 1| < ε → |g 2 - f 2| < ε →
        (g N, g (N + 1), g (N + 2)) ∈ U := by
  obtain ⟨x, hx⟩ := sf_surj P Q hQ0 N y
  have hcont : Continuous (fun x : ℝ × ℝ × ℝ => (sf P Q x N, sf P Q x (N + 1), sf P Q x (N + 2))) :=
    (sf_cont P Q N).1.prodMk ((sf_cont P Q N).2.1.prodMk (sf_cont P Q N).2.2)
  have hopen : IsOpen ((fun x : ℝ × ℝ × ℝ => (sf P Q x N, sf P Q x (N + 1), sf P Q x (N + 2))) ⁻¹' U) :=
    hU.preimage hcont
  have hxm : x ∈ (fun x : ℝ × ℝ × ℝ => (sf P Q x N, sf P Q x (N + 1), sf P Q x (N + 2))) ⁻¹' U := by
    simp only [Set.mem_preimage]; rw [hx]; exact hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x hxm
  refine ⟨solutionFrom P Q x.1 x.2.1 x.2.2, isSolution_from P Q _ _ _, ε, hε, ?_⟩
  intro g hg h0 h1 h2
  have hgx : (g 0, g 1, g 2) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [max_lt_iff]
    exact ⟨h0, h1, h2⟩
  have := hball hgx
  simp only [Set.mem_preimage] at this
  have e := sol_eq P Q g hg
  have e' : ∀ n, sf P Q (g 0, g 1, g 2) n = g n := fun n => (congrFun e n).symm
  simpa [e'] using this

theorem condI_pos (P Q : RatFunc ℝ) (N : ℕ)
    (hP : ∀ n : ℕ, N ≤ n → 0 < ev P n) (hPQ : ∀ n : ℕ, N ≤ n → -ev P n ≤ ev Q n)
    (g : ℕ → ℝ) (hg : IsSolution P Q g) (h0 : 0 < g N) (h1 : g N < g (N + 1))
    (h2 : g (N + 1) < g (N + 2)) : ∀ n, N ≤ n → 0 < g n := by
  have key : ∀ k : ℕ, 0 < g (N + k) ∧ g (N + k) < g (N + k + 1) ∧ g (N + k + 1) < g (N + k + 2) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1, h2⟩
    | succ k ih =>
      obtain ⟨a, b, c⟩ := ih
      have hp := hP (N + k) (by omega)
      have hq := hPQ (N + k) (by omega)
      have hr : g (N + k + 3) = g (N + k + 2) + ev P ((N + k : ℕ) : ℝ) * g (N + k + 1) +
          ev Q ((N + k : ℕ) : ℝ) * g (N + k) := hg (N + k)
      have t1 : 0 < ev P ((N + k : ℕ) : ℝ) * (g (N + k + 1) - g (N + k)) :=
        mul_pos hp (by linarith)
      have t2 : 0 ≤ (ev Q ((N + k : ℕ) : ℝ) + ev P ((N + k : ℕ) : ℝ)) * g (N + k) :=
        mul_nonneg (by linarith) a.le
      show 0 < g (N + k + 1) ∧ g (N + k + 1) < g (N + k + 2) ∧ g (N + k + 2) < g (N + k + 3)
      refine ⟨by linarith, c, ?_⟩
      nlinarith
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact (key k).1

theorem condI_robust (P Q : RatFunc ℝ) (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (h : ConditionI P Q) :
    AdmitsRobustlyUltimatelyPositiveSolution P Q := by
  obtain ⟨hlim, hge⟩ := h
  have hPev : ∀ᶠ x : ℝ in Filter.atTop, 0 < ev P x := by
    rcases hlim with ⟨l, hl1, hl⟩ | hl
    · exact hl.eventually_const_lt (by linarith : (0 : ℝ) < l)
    · exact hl.eventually_gt_atTop 0
  obtain ⟨M1, hM1⟩ := Filter.eventually_atTop.1 hPev
  obtain ⟨M2, hM2⟩ := Filter.eventually_atTop.1 hge
  set N : ℕ := ⌈max M1 M2⌉₊ with hN
  have hNM : ∀ n : ℕ, N ≤ n → max M1 M2 ≤ (n : ℝ) := by
    intro n hn
    have h1 : max M1 M2 ≤ ⌈max M1 M2⌉₊ := Nat.le_ceil _
    have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hP : ∀ n : ℕ, N ≤ n → 0 < ev P n := fun n hn =>
    hM1 n (le_trans (le_max_left _ _) (hNM n hn))
  have hPQ : ∀ n : ℕ, N ≤ n → -ev P n ≤ ev Q n := fun n hn =>
    hM2 n (le_trans (le_max_right _ _) (hNM n hn))
  let U : Set (ℝ × ℝ × ℝ) := {y | 0 < y.1 ∧ y.1 < y.2.1 ∧ y.2.1 < y.2.2}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_and]
    refine (isOpen_lt continuous_const continuous_fst).inter ?_
    refine (isOpen_lt continuous_fst (continuous_fst.comp continuous_snd)).inter ?_
    exact isOpen_lt (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)
  obtain ⟨f, hf, ε, hε, hrob⟩ := exists_robust P Q hQ0 N U hU (1, 2, 3)
    (by refine ⟨?_, ?_, ?_⟩ <;> norm_num)
  refine ⟨f, hf, ε, hε, fun g hg h0 h1 h2 => ?_⟩
  obtain ⟨a, b, c⟩ := hrob g hg h0 h1 h2
  exact ⟨N, condI_pos P Q N hP hPQ g hg a b c⟩

theorem condII_robust (P Q : RatFunc ℝ) (hP : NoPolesOnNat P) (hQ : NoPolesOnNat Q)
    (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (h : ConditionII P Q) :
    AdmitsRobustlyUltimatelyPositiveSolution P Q := by
  obtain ⟨S, L, N, -, hmain⟩ := HolonomicPositivity.Robust.lemma_5_1 P Q hP hQ hQ0 h
  let U : Set (ℝ × ℝ × ℝ) := {y | 0 < y.1 ∧ 0 < y.2.1 - ev S (N : ℝ) * y.1 ∧
    0 < y.2.2 - ev S ((N + 1 : ℕ) : ℝ) * y.2.1 - ev L (N : ℝ) * (y.2.1 - ev S (N : ℝ) * y.1)}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_and]
    refine (isOpen_lt continuous_const continuous_fst).inter ?_
    refine (isOpen_lt continuous_const (by fun_prop)).inter ?_
    exact isOpen_lt continuous_const (by fun_prop)
  obtain ⟨f, hf, ε, hε, hrob⟩ := exists_robust P Q hQ0 N U hU
    (1, ev S (N : ℝ) + 1, ev S ((N + 1 : ℕ) : ℝ) * (ev S (N : ℝ) + 1) + ev L (N : ℝ) * 1 + 1)
    (by refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> linarith)
  refine ⟨f, hf, ε, hε, fun g hg h0 h1 h2 => ?_⟩
  obtain ⟨a, b, c⟩ := hrob g hg h0 h1 h2
  have hc0 : Certificate S L g N := ⟨a, b, c⟩
  have key : ∀ k : ℕ, Certificate S L g (N + k) := by
    intro k
    induction k with
    | zero => exact hc0
    | succ k ih => exact hmain g hg (N + k) (by omega) ih
  exact ⟨N, fun n hn => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (key k).1⟩

end HolonomicPositivity.Dev.T31
namespace HolonomicPositivity.Robust
open HolonomicPositivity.Dev.T31 in
theorem chk_theorem_3_1 (P Q : RatFunc ℝ) (hP : NoPolesOnNat P) (hQ : NoPolesOnNat Q)
    (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (h : ConditionI P Q ∨ ConditionII P Q) :
    AdmitsRobustlyUltimatelyPositiveSolution P Q := by
  rcases h with h | h
  · exact condI_robust P Q hQ0 h
  · exact condII_robust P Q hP hQ hQ0 h
end HolonomicPositivity.Robust
end

theorem solution : type_of% @HolonomicPositivity.Robust.chk_theorem_3_1 := @HolonomicPositivity.Robust.chk_theorem_3_1
