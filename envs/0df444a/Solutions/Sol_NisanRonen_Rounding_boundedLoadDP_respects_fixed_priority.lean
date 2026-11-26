-- Prove2me | solution 1 for NisanRonen.Rounding.boundedLoadDP_respects_fixed_priority
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:49:46.026672+00:00
-- url     : https://prove2.me/submissions/86116055-da2e-4b58-a060-767df7522421

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

private def allocationRank {n : ℕ} : List (Fin n) → ℕ
  | [] => 0
  | j :: js => j.val + n * allocationRank js

private theorem allocationRank_inj {n : ℕ} [NeZero n] {l r : List (Fin n)}
    (hlen : l.length = r.length) (h : allocationRank l = allocationRank r) : l = r := by
  induction l generalizing r with
  | nil => simpa using hlen.symm
  | cons i l ih =>
    cases r with
    | nil => simp at hlen
    | cons j r =>
      have hij : i.val = j.val := by
        have hmod := congrArg (fun x : ℕ => x % n) h
        simpa only [allocationRank, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt,
          Nat.mod_eq_of_lt j.isLt] using hmod
      have hmul : n * allocationRank l = n * allocationRank r := by
        simpa [allocationRank, hij] using h
      have hr : allocationRank l = allocationRank r :=
        Nat.eq_of_mul_eq_mul_left (NeZero.pos n) hmul
      exact congrArg₂ List.cons (Fin.ext hij)
        (ih (Nat.succ.inj hlen) hr)

private def Before {n : ℕ} (x y : LoadState n) : Prop :=
  allocationRank x.2 < allocationRank y.2

private theorem keep_pairwise {n : ℕ} (l : List (LoadState n))
    (h : l.Pairwise Before) : (keepLoadStates l).Pairwise Before := by
  cases l with
  | nil => simp [keepLoadStates]
  | cons t l =>
    rw [List.pairwise_cons] at h
    rw [keepLoadStates, List.eraseDupsBy_cons, List.pairwise_cons]
    constructor
    · intro u hu
      have hm := (mem_keepLoadStates (show u ∈ keepLoadStates _ from hu))
      exact h.1 u (List.mem_filter.mp hm).1
    · exact keep_pairwise _ (h.2.filter _)
termination_by l.length
decreasing_by
  subst_vars
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem keep_rank_le {n : ℕ} (l : List (LoadState n))
    (h : l.Pairwise Before) (s : LoadState n) (hs : s ∈ l) :
    ∃ t ∈ keepLoadStates l, t.1 = s.1 ∧ allocationRank t.2 ≤ allocationRank s.2 := by
  cases l with
  | nil => simp at hs
  | cons t l =>
    rw [List.pairwise_cons] at h
    rw [keepLoadStates, List.eraseDupsBy_cons]
    by_cases hst : s.1 = t.1
    · refine ⟨t, List.mem_cons_self, hst.symm, ?_⟩
      rcases List.mem_cons.mp hs with e | e
      · rw [e]
      · exact (h.1 s e).le
    · have hs' : s ∈ l := (List.mem_cons.mp hs).resolve_left (fun he => hst (congrArg Prod.fst he))
      have hm : s ∈ l.filter (fun b => decide (decide (b.1 = t.1) = false)) := by simp [hs', hst]
      obtain ⟨u, hu, he, hRank⟩ := keep_rank_le _ (h.2.filter _) s hm
      exact ⟨u, List.mem_cons_of_mem _ hu, he, hRank⟩
termination_by l.length
decreasing_by
  subst_vars
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem extend_pairwise {n : ℕ} (col : Fin n → ℕ) (l : List (LoadState n))
    (h : l.Pairwise Before) :
    (l.flatMap fun s => (List.finRange n).map (prependJob col s)).Pairwise Before := by
  rw [List.pairwise_flatMap]
  constructor
  · intro s _
    rw [List.pairwise_map]
    apply (List.pairwise_lt_finRange n).imp
    intro i j hij
    have hv : i.val < j.val := hij
    change i.val + n * allocationRank s.2 < j.val + n * allocationRank s.2
    omega
  · apply h.imp
    intro s t hst x hx y hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    change i.val + n * allocationRank s.2 < j.val + n * allocationRank t.2
    have hmid : n * (allocationRank s.2 + 1) ≤ n * allocationRank t.2 :=
      Nat.mul_le_mul_left n hst
    have hi : i.val < n := i.isLt
    rw [Nat.mul_succ] at hmid
    omega

private theorem states_pairwise {n : ℕ} (columns : List (Fin n → ℕ)) :
    (loadStates columns).Pairwise Before := by
  induction columns with
  | nil => simp [loadStates]
  | cons col columns ih =>
    exact keep_pairwise _ (extend_pairwise col _ ih)

private theorem state_complete_rank {n : ℕ} (columns : List (Fin n → ℕ)) (agents : List (Fin n))
    (h : agents.length = columns.length) :
    ∃ s ∈ loadStates columns, s.1 = allocationLoads columns agents ∧
      allocationRank s.2 ≤ allocationRank agents := by
  induction columns generalizing agents with
  | nil =>
    have : agents = [] := List.length_eq_zero_iff.mp h
    subst agents
    exact ⟨(fun _ => 0, []), List.mem_cons_self, rfl, le_rfl⟩
  | cons col columns ih =>
    cases agents with
    | nil => simp at h
    | cons i agents =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      obtain ⟨s, hs, hload, hRank⟩ := ih agents h
      have hc : prependJob col s i ∈
          (loadStates columns).flatMap (fun state =>
            (List.finRange n).map (prependJob col state)) :=
        List.mem_flatMap.mpr ⟨s, hs, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩
      obtain ⟨t, ht, he, hb⟩ := keep_rank_le _ (extend_pairwise col _ (states_pairwise columns))
        (prependJob col s i) hc
      refine ⟨t, ht, he.trans ?_, hb.trans ?_⟩
      · funext j
        simp [prependJob, allocationLoads, hload]
      · exact Nat.add_le_add_left (Nat.mul_le_mul_left n hRank) i.val

private theorem sorted_argmin_rank {n : ℕ} {l : List (LoadState n)}
    (hl : l.Pairwise Before) {s t : LoadState n}
    (hs : s ∈ l.argmin (fun s => Finset.univ.sup s.1)) (ht : t ∈ l)
    (hscore : Finset.univ.sup t.1 ≤ Finset.univ.sup s.1) :
    allocationRank s.2 ≤ allocationRank t.2 := by
  classical
  letI : DecidableEq (LoadState n) := Classical.decEq _
  letI : BEq (LoadState n) := instBEqOfDecidableEq
  have hindex := List.index_of_argmin hs ht hscore
  have hsl : l.idxOf s < l.length := List.idxOf_lt_length_iff.mpr (List.argmin_mem hs)
  have htl : l.idxOf t < l.length := List.idxOf_lt_length_iff.mpr ht
  rcases lt_or_eq_of_le hindex with h | h
  · have hRank := List.pairwise_iff_getElem.mp hl (l.idxOf s) (l.idxOf t) hsl htl h
    rw [List.getElem_idxOf hsl, List.getElem_idxOf htl] at hRank
    exact hRank.le
  · have hlst : s = t := by
      calc
        s = l[l.idxOf s] := (List.getElem_idxOf hsl).symm
        _ = l[l.idxOf t] := by congr 1
        _ = t := List.getElem_idxOf htl
    rw [hlst]

theorem solution {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (n : ℕ) [NeZero n] (k : ℕ) :
    ∃ rank : (Fin k → Fin n) → ℕ, Function.Injective rank ∧
      ∀ d : Fin n → Fin k → ℝ, (∀ l j, a ≤ d l j ∧ d l j ≤ b) →
        let f := boundedLoadDP (n := n) (⌈b / δ⌉.toNat)
        let x := allocOf f δ d
        ∀ y : Fin k → Fin n, roundedMakespan δ y (corrStar y d) =
          roundedMakespan δ x (corrStar x d) → rank x ≤ rank y := by
  refine ⟨fun y => allocationRank (List.ofFn y), ?_, ?_⟩
  · intro y y' h
    exact List.ofFn_inj.mp (allocationRank_inj (by simp) h)
  intro d hd
  dsimp only
  intro y heq
  let cap := ⌈b / δ⌉.toNat
  let cols := units δ d
  let f := boundedLoadDP (n := n) cap
  let x := allocOf f δ d
  have hc : ∀ c ∈ cols, ∀ i, c i ≤ cap := by
    intro c h i
    change c ∈ units δ d at h
    rw [units, List.mem_ofFn] at h
    obtain ⟨j, rfl⟩ := h
    exact Int.toNat_le_toNat (Int.ceil_mono (div_le_div_of_nonneg_right (hd i j).2 hδ.le))
  have hcap : (cols.all fun column =>
      (List.finRange n).all (fun i => decide (column i ≤ cap))) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact fun c h i _ => hc c h i
  have hlen (z : Fin k → Fin n) : (List.ofFn z).length = cols.length := by simp [cols, units]
  obtain ⟨t, ht, htload, htRank⟩ := state_complete_rank cols (List.ofFn y) (hlen y)
  cases harg : (loadStates cols).argmin (fun s => Finset.univ.sup s.1) with
  | none => simp [List.argmin_eq_none.mp harg] at ht
  | some s =>
    have hs : s ∈ (loadStates cols).argmin (fun s => Finset.univ.sup s.1) := by simp [harg]
    have hf : f cols = s.2 := by simp [f, boundedLoadDP, hcap, harg]
    rcases state_sound (List.argmin_mem hs) with ⟨hslen, hsload⟩
    have hx : List.ofFn x = s.2 := by
      apply List.ext_getElem
      · exact (hlen x).trans hslen.symm
      · intro j h₁ h₂
        simp [x, allocOf, ← show cols = units δ d from rfl, hf, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem h₂]
    have hunit : Finset.univ.sup (allocationLoads cols (List.ofFn y)) =
        Finset.univ.sup (allocationLoads cols (List.ofFn x)) := by
      change roundedMakespan δ y (corrStar y d) = roundedMakespan δ x (corrStar x d) at heq
      rw [roundedMakespan_eq_unit ha hδ d (fun i j => (hd i j).1),
        roundedMakespan_eq_unit ha hδ d (fun i j => (hd i j).1)] at heq
      exact_mod_cast (mul_left_cancel₀ hδ.ne' heq)
    have hscore : Finset.univ.sup t.1 ≤ Finset.univ.sup s.1 := by
      rw [htload, hsload, hunit, hx]
    change allocationRank (List.ofFn x) ≤ allocationRank (List.ofFn y)
    rw [hx]
    exact (sorted_argmin_rank (states_pairwise cols) hs ht hscore).trans htRank
