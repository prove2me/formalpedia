-- Prove2me | solution 1 for NisanRonen.Rounding.boundedLoadDP_exact
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:35:47.586149+00:00
-- url     : https://prove2.me/submissions/d7dd3ae1-0310-4ddd-9772-48895236ed8e

import Definitions.Def_NisanRonen_Rounding_boundedLoadDP
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

open NisanRonen.Rounding
set_option autoImplicit false

private def allocationLoads {n : ℕ} :
    List (Fin n → ℕ) → List (Fin n) → Fin n → ℕ
  | column :: columns, agent :: agents, i =>
      (if i = agent then column i else 0) + allocationLoads columns agents i
  | _, _, _ => 0

private theorem mem_keepLoadStates {n : ℕ} {states : List (LoadState n)} {s : LoadState n}
    (h : s ∈ keepLoadStates states) : s ∈ states := by
  cases states with
  | nil => simp [keepLoadStates] at h
  | cons t states =>
    rw [keepLoadStates, List.eraseDupsBy_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · have hm := mem_keepLoadStates (show s ∈ keepLoadStates _ from h)
      exact List.mem_cons_of_mem t (List.mem_filter.mp hm).1
termination_by states.length
decreasing_by
  subst_vars
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem exists_kept_load {n : ℕ} {states : List (LoadState n)} {s : LoadState n}
    (h : s ∈ states) : ∃ t ∈ keepLoadStates states, t.1 = s.1 := by
  cases states with
  | nil => simp at h
  | cons t states =>
    rw [keepLoadStates, List.eraseDupsBy_cons]
    by_cases hst : s.1 = t.1
    · exact ⟨t, List.mem_cons_self, hst.symm⟩
    · have hs : s ∈ states := (List.mem_cons.mp h).resolve_left (fun he => hst (congrArg Prod.fst he))
      have hm : s ∈ states.filter (fun b => decide (decide (b.1 = t.1) = false)) := by
        simp [hs, hst]
      obtain ⟨u, hu, he⟩ := exists_kept_load hm
      exact ⟨u, List.mem_cons_of_mem _ hu, he⟩
termination_by states.length
decreasing_by
  subst_vars
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem state_sound {n : ℕ} {columns : List (Fin n → ℕ)} {s : LoadState n}
    (h : s ∈ loadStates columns) :
    s.2.length = columns.length ∧ s.1 = allocationLoads columns s.2 := by
  induction columns generalizing s with
  | nil =>
    simp only [loadStates, List.mem_singleton] at h
    subst s
    exact ⟨rfl, rfl⟩
  | cons column columns ih =>
    rw [loadStates] at h
    obtain ⟨t, ht, hs⟩ := List.mem_flatMap.mp (mem_keepLoadStates h)
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hlen, hload⟩ := ih ht
    refine ⟨by simp [prependJob, hlen], ?_⟩
    funext j
    simp [prependJob, allocationLoads, hload]

private theorem state_complete {n : ℕ} (columns : List (Fin n → ℕ)) (agents : List (Fin n))
    (h : agents.length = columns.length) :
    ∃ s ∈ loadStates columns, s.1 = allocationLoads columns agents := by
  induction columns generalizing agents with
  | nil =>
    have : agents = [] := List.length_eq_zero_iff.mp h
    subst agents
    exact ⟨(fun _ => 0, []), List.mem_cons_self, rfl⟩
  | cons column columns ih =>
    cases agents with
    | nil => simp at h
    | cons i agents =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      obtain ⟨s, hs, hload⟩ := ih agents h
      have hc : prependJob column s i ∈
          (loadStates columns).flatMap (fun state =>
            (List.finRange n).map (prependJob column state)) :=
        List.mem_flatMap.mpr ⟨s, hs, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩
      obtain ⟨t, ht, he⟩ := exists_kept_load hc
      refine ⟨t, ht, he.trans ?_⟩
      funext j
      simp [prependJob, allocationLoads, hload]

private theorem boundedLoadDP_optimal {n : ℕ} [NeZero n] (cap : ℕ)
    (columns : List (Fin n → ℕ))
    (hc : ∀ c ∈ columns, ∀ i, c i ≤ cap) :
    (boundedLoadDP cap columns).length = columns.length ∧
      ∀ agents : List (Fin n), agents.length = columns.length →
      Finset.univ.sup (allocationLoads columns (boundedLoadDP cap columns)) ≤
        Finset.univ.sup (allocationLoads columns agents) := by
  have hcap : (columns.all fun column =>
      (List.finRange n).all (fun i => decide (column i ≤ cap))) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact fun c h i _ => hc c h i
  obtain ⟨s₀, hs₀, _⟩ := state_complete columns (columns.map fun _ => (0 : Fin n)) (by simp)
  unfold boundedLoadDP
  rw [if_pos hcap]
  cases hs : (loadStates columns).argmin (fun s => Finset.univ.sup s.1) with
  | none => simp [List.argmin_eq_none.mp hs] at hs₀
  | some s =>
    have hm : s ∈ (loadStates columns).argmin (fun s => Finset.univ.sup s.1) := by
      simp [hs]
    rcases state_sound (List.argmin_mem hm) with ⟨hlen, hload⟩
    simp only [Option.map_some, Option.getD_some]
    refine ⟨hlen, fun agents hlen' => ?_⟩
    obtain ⟨t, ht, hload'⟩ := state_complete columns agents hlen'
    simpa only [hload, hload'] using List.le_of_mem_argmin ht hm

private theorem allocationLoads_ofFn {n k : ℕ} (column : Fin k → Fin n → ℕ)
    (x : Fin k → Fin n) (i : Fin n) :
    allocationLoads (List.ofFn column) (List.ofFn x) i =
      ∑ j : Fin k, if i = x j then column j i else 0 := by
  induction k with
  | zero => simp [allocationLoads]
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Fin.sum_univ_succ, allocationLoads, ih]

private theorem roundedMakespan_eq_unit {n k : ℕ} [NeZero n] {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (d : Fin n → Fin k → ℝ) (hd : ∀ i j, a ≤ d i j)
    (x : Fin k → Fin n) :
    roundedMakespan δ x (corrStar x d) =
      δ * ((Finset.univ.sup (allocationLoads (units δ d) (List.ofFn x)) : ℕ) : ℝ) := by
  have hload (i : Fin n) :
      load x (fun j => roundUp δ (corrStar x d j)) i =
        δ * (allocationLoads (units δ d) (List.ofFn x) i : ℝ) := by
    rw [units, allocationLoads_ofFn]
    push_cast
    rw [Finset.mul_sum, load, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : x j = i
    · have hceil : 0 ≤ ⌈d i j / δ⌉ :=
        Int.ceil_nonneg (div_nonneg (ha.le.trans (hd i j)) hδ.le)
      have hcast : (↑⌈d i j / δ⌉ : ℝ) = (⌈d i j / δ⌉.toNat : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hceil).symm
      simp [hj, corrStar, roundUp, hcast]
    · simp [hj, Ne.symm hj]
  have hs (i : Fin n) :
      load x (fun j => roundUp δ (corrStar x d j)) i ≤
        δ * ((Finset.univ.sup (allocationLoads (units δ d) (List.ofFn x)) : ℕ) : ℝ) := by
    rw [hload]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.le_sup (f :=
      allocationLoads (units δ d) (List.ofFn x)) (Finset.mem_univ i)) hδ.le
  unfold roundedMakespan makespan
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _ => hs i)
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (allocationLoads (units δ d) (List.ofFn x))
    rw [← Finset.sup'_eq_sup Finset.univ_nonempty, hmax, ← hload]
    exact Finset.le_sup' _ hi

private theorem boundedLoadDP_exact {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (n : ℕ) [NeZero n] :
    IsExactRoundedSolver (boundedLoadDP (n := n) (⌈b / δ⌉.toNat)) δ a b := by
  intro k d hd
  let f := boundedLoadDP (n := n) (⌈b / δ⌉.toNat)
  have hc : ∀ c ∈ units δ d, ∀ i, c i ≤ ⌈b / δ⌉.toNat := by
    intro c hc i
    rw [units, List.mem_ofFn] at hc
    obtain ⟨j, rfl⟩ := hc
    exact Int.toNat_le_toNat (Int.ceil_mono (div_le_div_of_nonneg_right (hd i j).2 hδ.le))
  obtain ⟨hlen, hopt⟩ := boundedLoadDP_optimal _ (units δ d) hc
  have hlen' : (f (units δ d)).length = k := hlen.trans List.length_ofFn
  refine ⟨hlen', fun y => ?_⟩
  rw [roundedMakespan_eq_unit ha hδ d (fun i j => (hd i j).1),
    roundedMakespan_eq_unit ha hδ d (fun i j => (hd i j).1)]
  have hx : List.ofFn (allocOf f δ d) = f (units δ d) := by
    apply List.ext_getElem
    · simp [hlen']
    · intro j h₁ h₂
      simp [allocOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
  rw [hx]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hopt (List.ofFn y) (by simp [units])) hδ.le

theorem solution {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (n : ℕ) [NeZero n] :
    IsExactRoundedSolver (boundedLoadDP (n := n) (⌈b / δ⌉.toNat)) δ a b :=
  boundedLoadDP_exact ha hδ n

