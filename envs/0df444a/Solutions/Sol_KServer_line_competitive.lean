-- Prove2me | solution 1 for KServer.line_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T04:26:50.335731+00:00
-- url     : https://prove2.me/submissions/841dc98a-11bd-417c-bb26-b62f0854768a

import Mathlib
import Definitions.Def_KServer_model
import Theorems.Thm_KServer_dc_step
import Theorems.Thm_KServer_sorted_matching_le
import Theorems.Thm_KServer_competitive_of_schedule_bound

open KServer

private theorem moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

theorem solution (k : ℕ) (hk : 1 ≤ k) (C₀ : Config k ℝ) :
    ∃ A : OnlineAlgorithm k ℝ, A.conf [] = C₀ ∧ IsCompetitive A (k : ℝ) := by
  classical
  have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
  have hmc : ∀ u v : Fin k → ℝ, moveCost u v = ∑ i, |u i - v i| := by
    intro u v; unfold moveCost; exact Finset.sum_congr rfl fun i _ => Real.dist_eq _ _
  set x₀ : Fin k → ℝ := C₀ ∘ Tuple.sort C₀ with hx₀def
  have hx₀ : Monotone x₀ := Tuple.monotone_sort C₀
  -- the Double Coverage step, made into a total function
  have hchoice : ∀ (x : Fin k → ℝ) (r : ℝ), ∃ x' : Fin k → ℝ,
      Monotone x → (Monotone x' ∧ (∃ i, x' i = r) ∧
        ∀ y : Fin k → ℝ, Monotone y → (∃ m, y m = r) →
          moveCost x x' + ((k:ℝ) * (∑ i, |x' i - y i|) + ∑ i, ∑ j, max (x' j - x' i) 0)
            ≤ (k:ℝ) * (∑ i, |x i - y i|) + ∑ i, ∑ j, max (x j - x i) 0) := by
    intro x r
    by_cases hx : Monotone x
    · obtain ⟨x', h1, h2, h3⟩ := dc_step k hk x hx r
      exact ⟨x', fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨x, fun hc => absurd hc hx⟩
  choose step hstep using hchoice
  -- the trajectory of Double Coverage, started at the sorted initial configuration
  set traj : List ℝ → Fin k → ℝ := fun l =>
    List.reverseRecOn l x₀ (fun l r prev => step prev r) with htrajdef
  have htraj_nil : traj [] = x₀ := by simp [htrajdef]
  have htraj_concat : ∀ (l : List ℝ) (r : ℝ), traj (l ++ [r]) = step (traj l) r := by
    intro l r; simp [htrajdef]
  have htraj_mono : ∀ l : List ℝ, Monotone (traj l) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => rw [htraj_nil]; exact hx₀
    | append_singleton l r ih => rw [htraj_concat]; exact (hstep (traj l) r ih).1
  set conf : List ℝ → Config k ℝ := fun l => if l = [] then C₀ else traj l with hconfdef
  have hconf_nil : conf [] = C₀ := by simp [hconfdef]
  have hconf_ne : ∀ l : List ℝ, l ≠ [] → conf l = traj l := by
    intro l hl; simp [hconfdef, hl]
  have hserves : ∀ (l : List ℝ) (r : ℝ), ∃ i, conf (l ++ [r]) i = r := by
    intro l r
    rw [hconf_ne _ (by simp), htraj_concat]
    exact (hstep (traj l) r (htraj_mono l)).2.1
  refine ⟨⟨conf, hserves⟩, hconf_nil, ?_⟩
  refine competitive_of_schedule_bound k hk ℝ ⟨conf, hserves⟩ (k:ℝ)
    (moveCost C₀ x₀ + ∑ i, ∑ j, max (x₀ j - x₀ i) 0) hk0 ?_
  intro σ S hSch
  obtain ⟨hS0, hSserve⟩ := hSch
  have hS0' : S 0 = C₀ := by rw [hS0]; exact hconf_nil
  set ys : ℕ → Fin k → ℝ := fun j => S j ∘ Tuple.sort (S j) with hysdef
  have hys_mono : ∀ j, Monotone (ys j) := fun j => Tuple.monotone_sort (S j)
  set Ph : ℕ → ℝ := fun j =>
    (k:ℝ) * (∑ i, |traj (σ.take j) i - ys j i|)
      + ∑ i, ∑ i', max (traj (σ.take j) i' - traj (σ.take j) i) 0 with hPhdef
  have hPh_nonneg : ∀ j, 0 ≤ Ph j := by
    intro j
    have h1 : (0:ℝ) ≤ ∑ i, |traj (σ.take j) i - ys j i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    have h2 : (0:ℝ) ≤ ∑ i, ∑ i', max (traj (σ.take j) i' - traj (σ.take j) i) 0 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => le_max_right _ _
    have h3 := mul_nonneg hk0 h1
    simp only [hPhdef]
    linarith
  have hPh0 : Ph 0 = ∑ i, ∑ j, max (x₀ j - x₀ i) 0 := by
    have hy0 : ys 0 = x₀ := by rw [hysdef, hx₀def]; simp [hS0']
    simp only [hPhdef, List.take_zero, htraj_nil, hy0]
    simp
  -- THE TELESCOPING
  have key : ∀ m : ℕ, m ≤ σ.length →
      (∑ j ∈ Finset.range m, moveCost (traj (σ.take j)) (traj (σ.take (j+1)))) + Ph m
        ≤ Ph 0 + (k:ℝ) * ∑ j ∈ Finset.range m, moveCost (S j) (S (j+1)) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hm' : m < σ.length := by omega
      have ihm := ih (by omega)
      set r : ℝ := σ.get ⟨m, hm'⟩ with hrdef
      have htake : σ.take (m+1) = σ.take m ++ [r] := by
        rw [List.take_succ, List.getElem?_eq_getElem hm']
        rfl
      have htrajS : traj (σ.take (m+1)) = step (traj (σ.take m)) r := by
        rw [htake, htraj_concat]
      have hcov : ∃ i, ys (m+1) i = r := by
        obtain ⟨i, hi⟩ := hSserve ⟨m, hm'⟩
        refine ⟨(Tuple.sort (S (m+1))).symm i, ?_⟩
        rw [hysdef]
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
        exact hi
      have hdc := (hstep (traj (σ.take m)) r (htraj_mono _)).2.2 (ys (m+1))
        (hys_mono (m+1)) hcov
      have hadv : ∑ i, |traj (σ.take m) i - ys (m+1) i|
          ≤ (∑ i, |traj (σ.take m) i - ys m i|) + moveCost (S m) (S (m+1)) := by
        have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
          abs_sub_le (traj (σ.take m) i) (ys m i) (ys (m+1) i))
        rw [Finset.sum_add_distrib] at h2
        have h3 : ∑ i, |ys m i - ys (m+1) i| ≤ moveCost (S m) (S (m+1)) := by
          rw [hmc, hysdef]
          exact sorted_matching_le k (S m) (S (m+1))
        linarith
      have hmul : (k:ℝ) * (∑ i, |traj (σ.take m) i - ys (m+1) i|)
          ≤ (k:ℝ) * (∑ i, |traj (σ.take m) i - ys m i|)
            + (k:ℝ) * moveCost (S m) (S (m+1)) := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left hadv hk0
      have hstep' : moveCost (traj (σ.take m)) (traj (σ.take (m+1))) + Ph (m+1)
          ≤ Ph m + (k:ℝ) * moveCost (S m) (S (m+1)) := by
        simp only [hPhdef]
        rw [htrajS]
        linarith [hdc, hmul]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
      linarith [ihm, hstep']
  -- THE ALGORITHM'S COST VERSUS THE TRAJECTORY'S
  have hcost : (⟨conf, hserves⟩ : OnlineAlgorithm k ℝ).cost σ
      ≤ moveCost C₀ x₀
        + ∑ j ∈ Finset.range σ.length, moveCost (traj (σ.take j)) (traj (σ.take (j+1))) := by
    show (∑ j ∈ Finset.range σ.length, moveCost (conf (σ.take j)) (conf (σ.take (j+1))))
      ≤ _
    cases hn : σ.length with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      have := moveCost_nonneg C₀ x₀
      linarith
    | succ m =>
      have hσne : σ ≠ [] := by intro h; rw [h] at hn; simp at hn
      have hne : ∀ j : ℕ, 1 ≤ j → σ.take j ≠ [] := by
        intro j hj h
        rw [List.take_eq_nil_iff] at h
        rcases h with h | h
        · omega
        · exact hσne h
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have e1 : ∀ i ∈ Finset.range m,
          moveCost (conf (σ.take (i+1))) (conf (σ.take (i+1+1)))
            = moveCost (traj (σ.take (i+1))) (traj (σ.take (i+1+1))) := by
        intro i _
        rw [hconf_ne _ (hne _ (by omega)), hconf_ne _ (hne _ (by omega))]
      rw [Finset.sum_congr rfl e1]
      have e2 : moveCost (conf (σ.take 0)) (conf (σ.take (0+1)))
          = moveCost C₀ (traj (σ.take 1)) := by
        simp only [List.take_zero, Nat.zero_add]
        rw [hconf_nil, hconf_ne _ (hne 1 le_rfl)]
      have e3 : moveCost (traj (σ.take 0)) (traj (σ.take (0+1)))
          = moveCost x₀ (traj (σ.take 1)) := by
        simp only [List.take_zero, Nat.zero_add]
        rw [htraj_nil]
      rw [e2, e3]
      have := moveCost_triangle C₀ x₀ (traj (σ.take 1))
      linarith
  have hkey := key σ.length le_rfl
  have hnn := hPh_nonneg σ.length
  rw [hPh0] at hkey
  linarith [hcost, hkey]
