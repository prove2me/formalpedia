-- Prove2me | solution 1 for KServer.chunk_system_base
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T09:45:44.971151+00:00
-- url     : https://prove2.me/submissions/b07a0e26-51b2-45da-ae66-d5e588330908

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_chunk_system

open KServer

private theorem ecost_concat {M : Type*} [MetricSpace M]
    (E : EvaderAlgorithm M) (l : List (Set M)) (S : Set M) :
    E.cost (l ++ [S]) = E.cost l + dist (E.pos l) (E.pos (l ++ [S])) := by
  unfold EvaderAlgorithm.cost
  have hlen : (l ++ [S]).length = l.length + 1 := by simp
  rw [hlen, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (le_refl _), List.take_length,
      List.take_of_length_le (by simp)]

private theorem ecost_mono {M : Type*} [MetricSpace M]
    (E : EvaderAlgorithm M) (l L : List (Set M)) : E.cost l ≤ E.cost (l ++ L) := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L S ih =>
    have h := ecost_concat E (l ++ L) S
    have hd : 0 ≤ dist (E.pos (l ++ L)) (E.pos (l ++ L ++ [S])) := dist_nonneg
    rw [← List.append_assoc]
    linarith

theorem solution (β : ℕ) (hβ : 1 ≤ β) (α : ℝ) (hα0 : 0 ≤ α) (w : ℕ)
    (hw : α * (w : ℝ) ^ 2 ≤ 1) :
    letI := pathMetric β
    dist (0 : Fin (β + 1)) (Fin.last β) = β ∧
    Nonempty (ChunkSystem (Fin (β + 1)) 0 (Fin.last β)
      (1 / 2) (3 / 2) (α * (w : ℝ) ^ 2 * β) (2 * β) ⌈α * β * (w : ℝ) ^ 2⌉₊) := by
  letI := pathMetric β
  classical
  -- distances in the path space
  have hdist : ∀ a b : Fin (β + 1), dist a b = |(a.val : ℝ) - (b.val : ℝ)| := by
    intro a b
    rfl
  have hd0 : dist (0 : Fin (β + 1)) (Fin.last β) = β := by
    rw [hdist]
    simp [Fin.last]
  refine ⟨hd0, ?_⟩
  -- the points and chunks
  set pt : ℕ → Fin (β + 1) := fun n => ⟨min n β, by omega⟩ with hpt
  set chunkFn : Fin β → List (Set (Fin (β + 1))) := fun j =>
    if j.val = 0 then [{pt 0}, {pt 1}] else [{pt (j.val + 1)}] with hchunk
  -- the flattened prefix ends at the request `{pt i}`
  have hstep : ∀ i : ℕ, ∀ hi : i < β,
      ((List.ofFn chunkFn).take (i + 1)).flatten
        = ((List.ofFn chunkFn).take i).flatten
          ++ ((if i = 0 then [{pt 0}] else []) ++ [{pt (i + 1)}]) := by
    intro i hi
    have hlen : i < (List.ofFn chunkFn).length := by simp [hi]
    have htake : (List.ofFn chunkFn).take (i + 1)
        = (List.ofFn chunkFn).take i ++ [(List.ofFn chunkFn).get ⟨i, hlen⟩] := by
      rw [List.take_succ]
      congr 1
      rw [List.getElem?_eq_getElem hlen]
      rfl
    have hget : (List.ofFn chunkFn).get ⟨i, hlen⟩ = chunkFn ⟨i, hi⟩ := by
      simp
    rw [htake, hget, List.flatten_append]
    congr 1
    rw [hchunk]
    by_cases h0 : i = 0
    · simp only [h0]
      rfl
    · have : (⟨i, hi⟩ : Fin β).val ≠ 0 := h0
      simp only [if_neg this, if_neg h0]
      rfl
  -- the evader's position after the prefix `i+1` is pinned at `pt (i+1)`
  have hpin : ∀ (E : EvaderAlgorithm (Fin (β + 1))) (i : ℕ) (hi : i < β),
      E.pos (((List.ofFn chunkFn).take (i + 1)).flatten) = pt (i + 1) := by
    intro E i hi
    rw [hstep i hi]
    have hne : ({pt (i + 1)} : Set (Fin (β + 1))).Nonempty := ⟨pt (i + 1), rfl⟩
    have h := E.serves (((List.ofFn chunkFn).take i).flatten
      ++ (if i = 0 then [{pt 0}] else [])) {pt (i + 1)} hne
    rw [← List.append_assoc] at *
    exact h
  -- one unit of distance between consecutive points
  have hd1 : ∀ i : ℕ, i < β → dist (pt i) (pt (i + 1)) = 1 := by
    intro i hi
    rw [hdist, hpt]
    simp only
    have h1 : min i β = i := by omega
    have h2 : min (i + 1) β = i + 1 := by omega
    rw [h1, h2]
    push_cast
    rw [abs_of_nonpos (by linarith)]
    ring
  -- chunk shapes
  have hchunk0 : ∀ j : Fin β, j.val = 0 → chunkFn j = [{pt 0}, {pt 1}] := by
    intro j hj
    rw [hchunk]
    show (if j.val = 0 then [{pt 0}, {pt 1}] else [{pt (j.val + 1)}]) = [{pt 0}, {pt 1}]
    rw [if_pos hj]
  have hchunkN : ∀ j : Fin β, j.val ≠ 0 → chunkFn j = [{pt (j.val + 1)}] := by
    intro j hj
    rw [hchunk]
    show (if j.val = 0 then [{pt 0}, {pt 1}] else [{pt (j.val + 1)}]) = [{pt (j.val + 1)}]
    rw [if_neg hj]
  -- the full flattened sequence is the singletons in order
  have hflat : ∀ i : ℕ, 1 ≤ i → i ≤ β →
      ((List.ofFn chunkFn).take i).flatten
        = List.map (fun n => ({pt n} : Set (Fin (β + 1)))) (List.range (i + 1)) := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ hle
      by_cases hi0 : i = 0
      · subst hi0
        have h := hstep 0 (by omega)
        rw [h]
        simp
        rfl
      · have hi1 : 1 ≤ i := by omega
        have h := hstep i (by omega)
        rw [h, ih hi1 (by omega), if_neg hi0]
        rw [List.range_succ (n := i + 1), List.map_append]
        simp
  have hfull : (List.ofFn chunkFn).flatten
      = List.map (fun n => ({pt n} : Set (Fin (β + 1)))) (List.range (β + 1)) := by
    have h := hflat β hβ (le_refl β)
    rw [List.take_of_length_le (by simp)] at h
    exact h
  have hlen : ((List.ofFn chunkFn).flatten).length = β + 1 := by
    rw [hfull]
    simp
  -- the chunk system
  refine ⟨⟨Unit, fun _ => 1, β, fun _ => chunkFn, fun _ _ => 1,
    fun _ => zero_le_one, by simp, ?_, by omega, ?_, ?_, ?_, ?_, fun _ _ _ _ => rfl, ?_, ?_⟩⟩
  · -- mLo ≤ m
    have h1 : α * β * (w : ℝ) ^ 2 ≤ β := by nlinarith [Nat.cast_nonneg (α := ℝ) β]
    calc ⌈α * β * (w : ℝ) ^ 2⌉₊ ≤ ⌈(β : ℝ)⌉₊ := Nat.ceil_le_ceil h1
      _ = β := Nat.ceil_natCast β
  · -- nonemptiness of requests
    intro _ i S hS
    have hS' : S ∈ chunkFn i := hS
    by_cases h0 : i.val = 0
    · rw [hchunk0 i h0] at hS'
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hS'
      rcases hS' with h | h
      · exact h ▸ ⟨pt 0, rfl⟩
      · exact h ▸ ⟨pt 1, rfl⟩
    · rw [hchunkN i h0] at hS'
      rw [List.mem_singleton] at hS'
      exact hS' ▸ ⟨pt (i.val + 1), rfl⟩
  · -- last request is {t}
    intro _
    have hptβ : pt β = Fin.last β := by
      rw [hpt]
      exact Fin.ext (by simp [Fin.last])
    have h2 : (List.ofFn chunkFn).flatten
        = List.map (fun n => ({pt n} : Set (Fin (β + 1)))) (List.range β) ++ [{pt β}] := by
      rw [hfull, List.range_succ, List.map_append]
      rfl
    rw [h2, List.getLast?_concat, hptβ]
  · -- offline cost
    intro _
    have hQfeas : EvaderServes (0 : Fin (β + 1)) ((List.ofFn chunkFn).flatten)
        (fun j => if j = 0 then (0 : Fin (β + 1)) else pt (j - 1)) := by
      constructor
      · simp
      · intro j hne'
        have hj : (j : ℕ) < β + 1 := lt_of_lt_of_le j.2 (le_of_eq hlen)
        have hget : ((List.ofFn chunkFn).flatten).get j = {pt (j : ℕ)} := by
          have hj' : (j : ℕ) < ((List.ofFn chunkFn).flatten).length := j.2
          have h2 := List.getElem_of_eq hfull hj'
          rw [List.get_eq_getElem, h2, List.getElem_map, List.getElem_range]
        rw [hget]
        simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _)]
        rfl
    have hmem : (∑ j ∈ Finset.range ((List.ofFn chunkFn).flatten).length,
        dist ((fun j => if j = 0 then (0 : Fin (β + 1)) else pt (j - 1)) j)
          ((fun j => if j = 0 then (0 : Fin (β + 1)) else pt (j - 1)) (j + 1)))
        ∈ {c : ℝ | ∃ Q : ℕ → Fin (β + 1),
            EvaderServes 0 ((List.ofFn chunkFn).flatten) Q ∧
            c = ∑ j ∈ Finset.range ((List.ofFn chunkFn).flatten).length,
              dist (Q j) (Q (j + 1))} := ⟨_, hQfeas, rfl⟩
    have hbdd : BddBelow {c : ℝ | ∃ Q : ℕ → Fin (β + 1),
        EvaderServes 0 ((List.ofFn chunkFn).flatten) Q ∧
        c = ∑ j ∈ Finset.range ((List.ofFn chunkFn).flatten).length,
          dist (Q j) (Q (j + 1))} := by
      refine ⟨0, ?_⟩
      rintro c ⟨Q, -, rfl⟩
      exact Finset.sum_nonneg fun j _ => dist_nonneg
    have hval : (∑ j ∈ Finset.range ((List.ofFn chunkFn).flatten).length,
        dist ((fun j => if j = 0 then (0 : Fin (β + 1)) else pt (j - 1)) j)
          ((fun j => if j = 0 then (0 : Fin (β + 1)) else pt (j - 1)) (j + 1))) = β := by
      rw [hlen, Finset.sum_range_succ']
      have h0 : dist ((fun j => if j = 0 then (0 : Fin (β + 1)) else pt (j - 1)) 0)
          ((fun j => if j = 0 then (0 : Fin (β + 1)) else pt (j - 1)) 1) = 0 := by
        show dist (0 : Fin (β + 1)) (pt (1 - 1)) = 0
        have hpt0 : pt (1 - 1) = (0 : Fin (β + 1)) := by
          rw [hpt]
          exact Fin.ext (by simp)
        rw [hpt0, dist_self]
      have h1 : ∀ i ∈ Finset.range β,
          dist ((fun j => if j = 0 then (0 : Fin (β + 1)) else pt (j - 1)) (i + 1))
            ((fun j => if j = 0 then (0 : Fin (β + 1)) else pt (j - 1)) (i + 1 + 1)) = 1 := by
        intro i hi
        simp only [Finset.mem_range] at hi
        simp only [if_neg (Nat.succ_ne_zero _)]
        have e1 : i + 1 - 1 = i := by omega
        have e2 : i + 1 + 1 - 1 = i + 1 := by omega
        rw [e1, e2]
        exact hd1 i hi
      rw [Finset.sum_congr rfl h1, h0]
      simp
    calc evaderOfflineCost (0 : Fin (β + 1)) ((List.ofFn chunkFn).flatten)
        ≤ _ := csInf_le hbdd hmem
      _ = (β : ℝ) := hval
      _ ≤ dist (0 : Fin (β + 1)) (Fin.last β) := by rw [hd0]
  · -- size window
    intro _ _
    norm_num
  · -- the conditional cost bound
    intro i ω₀ E
    have hfilter : (Finset.univ.filter fun ω : Unit =>
        (List.ofFn ((fun _ => chunkFn) ω)).take i.val
          = (List.ofFn ((fun _ => chunkFn) ω₀)).take i.val) = Finset.univ := by
      refine Finset.filter_true_of_mem ?_
      intro ω _
      rfl
    rw [hfilter]
    have hsum1 : (∑ ω : Unit, (fun _ : Unit => (1 : ℝ)) ω) = 1 := by simp
    have hgoal : (1 : ℝ) ≤ E.escapeCost (((List.ofFn chunkFn).take i.val).flatten)
        (chunkFn i) (2 * β) := by
      unfold EvaderAlgorithm.escapeCost
      refine Finset.le_inf' _ _ ?_
      intro t ht
      simp only [Finset.mem_range] at ht
      set h : List (Set (Fin (β + 1))) := ((List.ofFn chunkFn).take i.val).flatten with hh
      have hcost0 : E.costOn h [] = 0 := by
        unfold EvaderAlgorithm.costOn
        rw [List.append_nil]
        ring
      have hcostnn : ∀ L, 0 ≤ E.costOn h L := by
        intro L
        unfold EvaderAlgorithm.costOn
        have := ecost_mono E h L
        linarith
      have h2β : (1 : ℝ) ≤ 2 * β := by
        have : (1 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ
        linarith
      by_cases hi0 : i.val = 0
      · -- chunk [{pt 0}, {pt 1}]
        have hc : chunkFn i = [{pt 0}, {pt 1}] := hchunk0 i hi0
        rw [hc] at ht ⊢
        have hlen2 : ([({pt 0} : Set (Fin (β + 1))), {pt 1}]).length = 2 := rfl
        rw [hlen2] at ht ⊢
        interval_cases t
        · rw [if_neg (by norm_num)]
          rw [List.take_zero, hcost0]
          linarith
        · rw [if_neg (by norm_num)]
          have := hcostnn ([({pt 0} : Set (Fin (β+1))), {pt 1}].take 1)
          linarith
        · rw [if_pos rfl]
          -- full service costs at least d(pt 0, pt 1) = 1
          have hhe : h = [] := by
            rw [hh, hi0]
            rfl
          have hsplit : ([({pt 0} : Set (Fin (β+1))), {pt 1}])
              = [({pt 0} : Set (Fin (β+1)))] ++ [{pt 1}] := rfl
          have hc1 : E.cost ([({pt 0} : Set (Fin (β+1)))] ++ [{pt 1}])
              = E.cost [({pt 0} : Set (Fin (β+1)))]
                + dist (E.pos [({pt 0} : Set (Fin (β+1)))])
                  (E.pos ([({pt 0} : Set (Fin (β+1)))] ++ [{pt 1}])) :=
            ecost_concat E _ _
          have hp0 : E.pos [({pt 0} : Set (Fin (β+1)))] = pt 0 := by
            have := E.serves [] {pt 0} ⟨pt 0, rfl⟩
            simpa using this
          have hp1 : E.pos ([({pt 0} : Set (Fin (β+1)))] ++ [{pt 1}]) = pt 1 := by
            have := E.serves [({pt 0} : Set (Fin (β+1)))] {pt 1} ⟨pt 1, rfl⟩
            simpa using this
          have hcost1 : 0 ≤ E.cost [({pt 0} : Set (Fin (β+1)))] := by
            have := ecost_mono E [] [({pt 0} : Set (Fin (β+1)))]
            unfold EvaderAlgorithm.cost at this ⊢
            simpa using this
          unfold EvaderAlgorithm.costOn
          rw [hhe, List.nil_append, hsplit, hc1, hp0, hp1, hd1 0 (by omega)]
          have hcnil : E.cost ([] : List (Set (Fin (β+1)))) = 0 := by
            unfold EvaderAlgorithm.cost
            simp
          rw [hcnil]
          linarith
      · -- chunk [{pt (i+1)}]
        have hc : chunkFn i = [{pt (i.val + 1)}] := hchunkN i hi0
        rw [hc] at ht ⊢
        have hlen1 : ([({pt (i.val + 1)} : Set (Fin (β + 1)))]).length = 1 := rfl
        rw [hlen1] at ht ⊢
        interval_cases t
        · rw [if_neg (by norm_num)]
          rw [List.take_zero, hcost0]
          linarith
        · rw [if_pos rfl]
          obtain ⟨i', hi'⟩ : ∃ i', i.val = i' + 1 := ⟨i.val - 1, by omega⟩
          have hpos : E.pos h = pt i.val := by
            rw [hh, hi']
            exact hpin E i' (by omega)
          have hcc : E.cost (h ++ [({pt (i.val + 1)} : Set (Fin (β+1)))])
              = E.cost h + dist (E.pos h)
                (E.pos (h ++ [({pt (i.val + 1)} : Set (Fin (β+1)))])) := ecost_concat E _ _
          have hp1 : E.pos (h ++ [({pt (i.val + 1)} : Set (Fin (β+1)))]) = pt (i.val + 1) := by
            have := E.serves h {pt (i.val + 1)} ⟨pt (i.val + 1), rfl⟩
            simpa using this
          unfold EvaderAlgorithm.costOn
          rw [hcc, hpos, hp1, hd1 i.val i.2]
          linarith
    calc (1 : ℝ) * (∑ ω : Unit, (fun _ : Unit => (1 : ℝ)) ω)
        = 1 := by rw [hsum1]; ring
      _ ≤ E.escapeCost (((List.ofFn chunkFn).take i.val).flatten) (chunkFn i) (2 * β) := hgoal
      _ = ∑ ω : Unit, (fun _ : Unit => (1 : ℝ)) ω
            * E.escapeCost (((List.ofFn ((fun _ => chunkFn) ω)).take i.val).flatten)
              ((fun _ => chunkFn) ω i) (2 * β) := by
          simp
  · -- expected total size
    have hsum : (∑ ω : Unit, (fun _ : Unit => (1 : ℝ)) ω * (∑ i : Fin β, (1 : ℝ))) = β := by
      simp
    rw [hsum]
    nlinarith [Nat.cast_nonneg (α := ℝ) β]
