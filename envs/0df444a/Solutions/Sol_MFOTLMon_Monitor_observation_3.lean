-- Prove2me | solution 1 for MFOTLMon.Monitor.observation_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T21:31:28.394095+00:00
-- url     : https://prove2.me/submissions/98c18bab-44a3-40dc-94ac-866003cfa245

import Definitions.Def_MFOTLMon_Monitor_Algorithm

namespace MFOTLMon.Monitor

namespace QueueProof

variable {S : Signature}

theorem run_zero (D : TempStruct S) (Φ : Formula S) : run D Φ 0 = init Φ := rfl

theorem run_succ (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    run D Φ (k + 1) = iteration D Φ (run D Φ k) := by
  exact Function.iterate_succ_apply' (iteration D Φ) k (init Φ)

theorem evalLoop_ell (D : TempStruct S) (Φ : Formula S) (fuel : ℕ) (s : State S) :
    (evalLoop D Φ fuel s).ell = s.ell := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      rw [evalLoop]
      split
      · exact ih _
      · rfl

theorem evalLoop_Q (D : TempStruct S) (Φ : Formula S) (fuel : ℕ) (s : State S) :
    (evalLoop D Φ fuel s).Q = s.Q := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      rw [evalLoop]
      split
      · exact ih _
      · rfl

theorem iteration_ell (D : TempStruct S) (Φ : Formula S) (s : State S) :
    (iteration D Φ s).ell = s.ell + 1 := by
  exact congrArg (fun n : ℕ ↦ n + 1) (evalLoop_ell D Φ (s.ell + 2) (afterBuild D s))

theorem iteration_Q (D : TempStruct S) (Φ : Formula S) (s : State S) :
    (iteration D Φ s).Q = updateQ D Φ s := by
  change updateQ D Φ (evalLoop D Φ (s.ell + 2) (afterBuild D s)) = updateQ D Φ s
  simp only [updateQ, evalLoop_Q, evalLoop_ell]
  rfl

theorem run_ell (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    (run D Φ k).ell = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [run_succ, iteration_ell, ih]

theorem mem_updateQ_fresh (D : TempStruct S) (Φ : Formula S) (s : State S)
    (α : Formula S) (hα : α ∈ tempSubs Φ) :
    (α, s.ell + 1, waitfor α) ∈ updateQ D Φ s := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨α, hα, rfl⟩

theorem mem_iteration_fresh (D : TempStruct S) (Φ : Formula S) (s : State S)
    (α : Formula S) (hα : α ∈ tempSubs Φ) :
    (α, s.ell + 1, waitfor α) ∈ (iteration D Φ s).Q := by
  change (α, s.ell + 1, waitfor α) ∈
    updateQ D Φ (evalLoop D Φ (s.ell + 2) (afterBuild D s))
  have hell : (evalLoop D Φ (s.ell + 2) (afterBuild D s)).ell = s.ell :=
    evalLoop_ell D Φ (s.ell + 2) (afterBuild D s)
  simpa only [hell] using
    mem_updateQ_fresh D Φ (evalLoop D Φ (s.ell + 2) (afterBuild D s)) α hα

theorem observation_one (D : TempStruct S) (Φ : Formula S) :
    ∀ α ∈ tempSubs Φ, ∀ k : ℕ, (α, k, waitfor α) ∈ (run D Φ k).Q := by
  intro α hα k
  cases k with
  | zero =>
      change (α, 0, waitfor α) ∈ (tempSubs Φ).map (fun β ↦ (β, 0, waitfor β))
      exact List.mem_map.mpr ⟨α, hα, rfl⟩
  | succ k =>
      rw [run_succ]
      simpa only [run_ell] using mem_iteration_fresh D Φ (run D Φ k) α hα

end QueueProof

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor.QueueProof

variable {S : Signature}

/-- Equal job keys carry equal waiting lists. This permits repeated identical occurrences. -/
def Coherent (Q : List (Formula S × ℕ × List (Formula S))) : Prop :=
  ∀ (α : Formula S) (j : ℕ) (U V : List (Formula S)),
    (α, j, U) ∈ Q → (α, j, V) ∈ Q → U = V

theorem mem_updateQ_cases (D : TempStruct S) (Φ : Formula S) (s : State S)
    (α : Formula S) (j : ℕ) (W : List (Formula S))
    (h : (α, j, W) ∈ updateQ D Φ s) :
    (∃ U, (α, j, U) ∈ s.Q ∧ U ≠ [] ∧
      W = (update U (D.τ (s.ell + 1) - D.τ s.ell)).flatMap waitfor) ∨
      (α ∈ tempSubs Φ ∧ j = s.ell + 1 ∧ W = waitfor α) := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨⟨β, m, U⟩, hmem, heq⟩ := List.mem_filterMap.mp h
    dsimp only at heq
    split at heq
    · cases heq
    · rename_i hU
      have heq' := Option.some.inj heq
      cases heq'
      exact Or.inl ⟨U, hmem, by simpa only [List.isEmpty_iff] using hU, rfl⟩
  · obtain ⟨β, hβ, heq⟩ := List.mem_map.mp h
    cases heq
    exact Or.inr ⟨hβ, rfl, rfl⟩

theorem updateQ_bounds (D : TempStruct S) (Φ : Formula S) (s : State S)
    (hbound : ∀ α j W, (α, j, W) ∈ s.Q → j ≤ s.ell) :
    ∀ α j W, (α, j, W) ∈ updateQ D Φ s → j ≤ s.ell + 1 := by
  intro α j W h
  rcases mem_updateQ_cases D Φ s α j W h with ⟨U, hU, _, _⟩ | ⟨_, hj, _⟩
  · exact (hbound α j U hU).trans (Nat.le_succ _)
  · exact hj.le

theorem updateQ_temporal (D : TempStruct S) (Φ : Formula S) (s : State S)
    (htemp : ∀ α j W, (α, j, W) ∈ s.Q → α ∈ tempSubs Φ) :
    ∀ α j W, (α, j, W) ∈ updateQ D Φ s → α ∈ tempSubs Φ := by
  intro α j W h
  rcases mem_updateQ_cases D Φ s α j W h with ⟨U, hU, _, _⟩ | ⟨hα, _, _⟩
  · exact htemp α j U hU
  · exact hα

theorem updateQ_coherent (D : TempStruct S) (Φ : Formula S) (s : State S)
    (hbound : ∀ α j W, (α, j, W) ∈ s.Q → j ≤ s.ell) (hcoh : Coherent s.Q) :
    Coherent (updateQ D Φ s) := by
  intro α j U V hU hV
  rcases mem_updateQ_cases D Φ s α j U hU with ⟨U', hU', _, rfl⟩ | ⟨_, hj, rfl⟩
  · rcases mem_updateQ_cases D Φ s α j V hV with ⟨V', hV', _, rfl⟩ | ⟨_, hj, _⟩
    · rw [hcoh α j U' V' hU' hV']
    · have := hbound α j U' hU'
      omega
  · rcases mem_updateQ_cases D Φ s α j V hV with ⟨V', hV', _, _⟩ | ⟨_, _, rfl⟩
    · have := hbound α j V' hV'
      omega
    · rfl

theorem run_queue_properties (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    (∀ α j W, (α, j, W) ∈ (run D Φ k).Q → j ≤ k) ∧
      (∀ α j W, (α, j, W) ∈ (run D Φ k).Q → α ∈ tempSubs Φ) ∧
      Coherent (run D Φ k).Q := by
  induction k with
  | zero =>
      constructor
      · intro α j W h
        obtain ⟨β, _, heq⟩ := List.mem_map.mp h
        cases heq
        exact Nat.le_refl 0
      · constructor
        · intro α j W h
          obtain ⟨β, hβ, heq⟩ := List.mem_map.mp h
          cases heq
          exact hβ
        · intro α j U V hU hV
          obtain ⟨β, _, hβ⟩ := List.mem_map.mp hU
          obtain ⟨γ, _, hγ⟩ := List.mem_map.mp hV
          cases hβ
          cases hγ
          rfl
  | succ k ih =>
      rw [run_succ, iteration_Q]
      have hbound : ∀ α j W, (α, j, W) ∈ (run D Φ k).Q →
          j ≤ (run D Φ k).ell := by
        simpa only [run_ell] using ih.1
      exact ⟨by simpa only [run_ell] using updateQ_bounds D Φ _ hbound,
        updateQ_temporal D Φ _ ih.2.1, updateQ_coherent D Φ _ hbound ih.2.2⟩

theorem run_queue_bounds (D : TempStruct S) (Φ : Formula S) (k : ℕ)
    (α : Formula S) (j : ℕ) (W : List (Formula S))
    (h : (α, j, W) ∈ (run D Φ k).Q) : j ≤ k :=
  (run_queue_properties D Φ k).1 α j W h

theorem run_queue_temporal (D : TempStruct S) (Φ : Formula S) (k : ℕ)
    (α : Formula S) (j : ℕ) (W : List (Formula S))
    (h : (α, j, W) ∈ (run D Φ k).Q) : α ∈ tempSubs Φ :=
  (run_queue_properties D Φ k).2.1 α j W h

theorem run_queue_coherent (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    Coherent (run D Φ k).Q := (run_queue_properties D Φ k).2.2

end MFOTLMon.Monitor.QueueProof

namespace MFOTLMon.Monitor.QueueProof

variable {S : Signature}

theorem set_p_frame (st : Store S) {α β : Formula S} {j m : ℕ}
    (X : Set (List ℕ)) (hne : (α, j) ≠ (β, m)) :
    (st.set (.p β) m X) (.p α) j = st (.p α) j := by
  simp only [Store.set]
  split
  · rename_i h
    exact (hne (Prod.ext (Key.p.inj h.1) h.2)).elim
  · rfl

theorem set_r_p_frame (st : Store S) (α β : Formula S) (j m : ℕ)
    (X : Set (List ℕ)) : (st.set (.r β) m X) (.p α) j = st (.p α) j := by
  simp [Store.set]

theorem set_s_p_frame (st : Store S) (α β : Formula S) (j m : ℕ)
    (X : Set (List ℕ)) : (st.set (.s β) m X) (.p α) j = st (.p α) j := by
  simp [Store.set]

theorem build_p_frame (D : TempStruct S) (st : Store S) (e : Formula S × ℕ)
    (α : Formula S) (j : ℕ) (hne : (α, j) ≠ e) :
    build D st e (.p α) j = st (.p α) j := by
  rcases e with ⟨β, m⟩
  cases β with
  | eq _ _ => rfl
  | pred _ _ => rfl
  | neg _ => rfl
  | or _ _ => rfl
  | ex _ _ => rfl
  | prev I β =>
      dsimp only [build]
      split
      · exact set_p_frame st _ hne
      · cases hatAt D st (m - 1) β with
        | none => rfl
        | some B => exact set_p_frame st _ hne
  | next I β =>
      dsimp only [build]
      cases hatAt D st (m + 1) β with
      | none => rfl
      | some B => exact set_p_frame st _ hne
  | since I β γ =>
      dsimp only [build]
      cases hatAt D st m β <;> cases hatAt D st m γ <;>
        cases (if m = 0 then some ∅ else st (.r (.since I β γ)) (m - 1)) <;> try rfl
      dsimp only
      rw [set_p_frame _ _ hne, set_r_p_frame]
  | «until» I β γ =>
      dsimp only [build]
      split
      · rw [set_p_frame _ _ hne, set_s_p_frame, set_r_p_frame]
      · rfl

theorem foldl_build_p_frame (D : TempStruct S) (L : List (Formula S × ℕ))
    (st : Store S) (α : Formula S) (j : ℕ)
    (hne : ∀ e ∈ L, (α, j) ≠ e) :
    (L.foldl (build D) st) (.p α) j = st (.p α) j := by
  induction L generalizing st with
  | nil => rfl
  | cons e L ih =>
      change (L.foldl (build D) (build D st e)) (.p α) j = st (.p α) j
      calc
        _ = build D st e (.p α) j := ih _ (fun e' he' ↦ hne e' (List.mem_cons_of_mem e he'))
        _ = st (.p α) j := build_p_frame D st e α j (hne e (List.mem_cons_self))

theorem afterBuild_p_frame (D : TempStruct S) (s : State S) (α : Formula S) (j : ℕ)
    (hne : ∀ β m, (β, m, ([] : List (Formula S))) ∈ s.Q → (α, j) ≠ (β, m)) :
    (afterBuild D s).store (.p α) j = s.store (.p α) j := by
  apply foldl_build_p_frame
  intro e he
  have he' := List.mem_mergeSort.mp he
  obtain ⟨⟨β, m, U⟩, hmem, heq⟩ := List.mem_map.mp he'
  obtain ⟨hmem, hempty⟩ := List.mem_filter.mp hmem
  have hU : U = [] := List.isEmpty_iff.mp hempty
  subst U
  cases heq
  exact hne β m hmem

theorem afterBuild_pending_none (D : TempStruct S) (s : State S)
    (hcoh : Coherent s.Q) (α : Formula S) (j : ℕ) (W : List (Formula S))
    (hmem : (α, j, W) ∈ s.Q) (hne : W ≠ []) (habs : s.store (.p α) j = none) :
    (afterBuild D s).store (.p α) j = none := by
  rw [afterBuild_p_frame D s α j]
  · exact habs
  · intro β m hready heq
    cases heq
    exact hne (hcoh α j W [] hmem hready)

theorem afterBuild_future_none (D : TempStruct S) (s : State S)
    (hbound : ∀ β m U, (β, m, U) ∈ s.Q → m ≤ s.ell)
    (hfuture : ∀ β m, s.ell ≤ m → s.store (.p β) m = none)
    (α : Formula S) (j : ℕ) (hj : s.ell < j) :
    (afterBuild D s).store (.p α) j = none := by
  rw [afterBuild_p_frame D s α j]
  · exact hfuture α j hj.le
  · intro β m hready heq
    have := hbound β m [] hready
    cases heq
    omega

theorem evalLoop_preserves_none (D : TempStruct S) (Φ : Formula S) (fuel : ℕ)
    (s : State S) (key : Key S) (j : ℕ) (habs : s.store key j = none) :
    (evalLoop D Φ fuel s).store key j = none := by
  induction fuel generalizing s with
  | zero => exact habs
  | succ fuel ih =>
      rw [evalLoop]
      split
      · apply ih
        change (if 0 < s.i then s.store.discard (s.i - 1) else s.store) key j = none
        split <;> simp [Store.discard, habs]
      · exact habs

theorem evalLoop_blocked (D : TempStruct S) (Φ : Formula S) (fuel : ℕ)
    (α : Formula S) (j : ℕ) (hα : α ∈ tempSubs Φ) (s : State S)
    (hij : s.i ≤ j) (habs : s.store (.p α) j = none) :
    (evalLoop D Φ fuel s).i ≤ j ∧
      (evalLoop D Φ fuel s).store (.p α) j = none := by
  induction fuel generalizing s with
  | zero => exact ⟨hij, habs⟩
  | succ fuel ih =>
      rw [evalLoop]
      split
      · rename_i hcomplete
        have hlt : s.i < j := by
          have hne : s.i ≠ j := by
            intro heq
            have hp := hcomplete.2 α hα
            rw [heq, habs] at hp
            cases hp
          omega
        apply ih
        · exact hlt
        · change (if 0 < s.i then s.store.discard (s.i - 1) else s.store) (.p α) j = none
          split <;> simp [Store.discard, habs]
      · exact ⟨hij, habs⟩

theorem run_pending_invariant (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    (∀ α j W, (α, j, W) ∈ (run D Φ k).Q →
      (run D Φ k).i ≤ j ∧ (run D Φ k).store (.p α) j = none) ∧
      (∀ α j, k ≤ j → (run D Φ k).store (.p α) j = none) := by
  induction k with
  | zero =>
      constructor
      · intro α j W _
        exact ⟨Nat.zero_le j, rfl⟩
      · intro α j _
        rfl
  | succ k ih =>
      have hbound : ∀ α j W, (α, j, W) ∈ (run D Φ k).Q →
          j ≤ (run D Φ k).ell := by
        simpa only [run_ell] using (run_queue_properties D Φ k).1
      have hfuture : ∀ α j, (run D Φ k).ell ≤ j →
          (run D Φ k).store (.p α) j = none := by
        simpa only [run_ell] using ih.2
      constructor
      · intro α j W hmem
        rw [run_succ, iteration_Q] at hmem
        rcases mem_updateQ_cases D Φ (run D Φ k) α j W hmem with
          ⟨U, hU, hne, _⟩ | ⟨hα, hj, _⟩
        · have hbefore := ih.1 α j U hU
          have habs := afterBuild_pending_none D _ (run_queue_coherent D Φ k)
            α j U hU hne hbefore.2
          have hblock := evalLoop_blocked D Φ (k + 2) α j
            (run_queue_temporal D Φ k α j U hU) (afterBuild D (run D Φ k))
            hbefore.1 habs
          simpa only [run_succ, iteration, run_ell] using hblock
        · have hbefore := ih.1 α k (waitfor α) (observation_one D Φ α hα k)
          have hj' : j = k + 1 := by simpa only [run_ell] using hj
          have habs := afterBuild_future_none D _ hbound hfuture α j (by
            rw [run_ell, hj']
            exact Nat.lt_succ_self k)
          have hij : (afterBuild D (run D Φ k)).i ≤ j := by
            change (run D Φ k).i ≤ j
            omega
          have hblock := evalLoop_blocked D Φ (k + 2) α j hα
            (afterBuild D (run D Φ k)) hij habs
          simpa only [run_succ, iteration, run_ell] using hblock
      · intro α j hj
        have habs := afterBuild_future_none D _ hbound hfuture α j (by
          rw [run_ell]
          omega)
        have hpres := evalLoop_preserves_none D Φ (k + 2)
          (afterBuild D (run D Φ k)) (.p α) j habs
        simpa only [run_succ, iteration, run_ell] using hpres

theorem observation_three (D : TempStruct S) (Φ : Formula S)
    (_huniq : TemporalSubformulasOnce Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S)),
      (α, j, W) ∈ (run D Φ k).Q → (run D Φ k).i ≤ j := by
  intro k α j W hmem
  exact ((run_pending_invariant D Φ k).1 α j W hmem).1

theorem run_i_le_of_temporal (D : TempStruct S) (Φ : Formula S) (k : ℕ)
    (α : Formula S) (hα : α ∈ tempSubs Φ) : (run D Φ k).i ≤ k :=
  ((run_pending_invariant D Φ k).1 α k (waitfor α) (observation_one D Φ α hα k)).1

theorem evalLoop_out_indices (D : TempStruct S) (Φ : Formula S) (fuel : ℕ) (s : State S)
    (hindices : s.out.map (fun e ↦ e.1) = List.range s.i) :
    (evalLoop D Φ fuel s).out.map (fun e ↦ e.1) = List.range (evalLoop D Φ fuel s).i := by
  induction fuel generalizing s with
  | zero => exact hindices
  | succ fuel ih =>
      rw [evalLoop]
      split
      · apply ih
        change (s.out ++ [_]).map (fun e : ℕ × Set (List ℕ) × ℕ ↦ e.1) =
          List.range (s.i + 1)
        simp only [List.map_append, hindices, List.map_cons, List.map_nil, List.range_succ]
      · exact hindices

theorem run_out_indices (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    (run D Φ k).out.map (fun e ↦ e.1) = List.range (run D Φ k).i := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [run_succ]
      exact evalLoop_out_indices D Φ _ (afterBuild D (run D Φ k)) ih

theorem run_output_exists_of_lt (D : TempStruct S) (Φ : Formula S) (k n : ℕ)
    (hn : n < (run D Φ k).i) :
    ∃ O t, (n, O, t) ∈ (run D Φ k).out := by
  have hmem : n ∈ (run D Φ k).out.map (fun e ↦ e.1) := by
    rw [run_out_indices]
    exact List.mem_range.mpr hn
  obtain ⟨⟨m, O, t⟩, hmem, heq⟩ := List.mem_map.mp hmem
  dsimp only at heq
  subst m
  exact ⟨O, t, hmem⟩

theorem run_output_lt (D : TempStruct S) (Φ : Formula S) (k n : ℕ)
    (O : Set (List ℕ)) (t : ℕ) (hmem : (n, O, t) ∈ (run D Φ k).out) :
    n < (run D Φ k).i := by
  have hmapped := List.mem_map_of_mem (f := fun e ↦ e.1) hmem
  rw [run_out_indices] at hmapped
  exact List.mem_range.mp hmapped

end MFOTLMon.Monitor.QueueProof

open MFOTLMon.Monitor

theorem solution {S : Signature} (D : TempStruct S) (Φ : Formula S)
    (huniq : TemporalSubformulasOnce Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S)), (α, j, W) ∈ (run D Φ k).Q →
      (run D Φ k).i ≤ j := by
  exact QueueProof.observation_three D Φ huniq
