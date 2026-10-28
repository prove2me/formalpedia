-- Prove2me | solution 1 for MFOTLMon.Monitor.observation_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T21:31:24.270883+00:00
-- url     : https://prove2.me/submissions/5f1e4590-19b2-40dc-a41b-3aa9dc2800db

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

def Future : Formula S → Prop
  | .next _ _ => True
  | .until _ _ _ => True
  | _ => False

def GoodWaiting (W : List (Formula S)) : Prop :=
  ∀ φ ∈ W, Bounded φ ∧ Future φ

def waitWeight : Formula S → ℕ
  | .eq _ _ => 0
  | .pred _ _ => 0
  | .neg β => waitWeight β
  | .ex _ β => waitWeight β
  | .prev _ β => waitWeight β
  | .or β γ => waitWeight β + waitWeight γ
  | .since _ β γ => waitWeight β + waitWeight γ
  | .next _ β => 1 + waitWeight β
  | .until I β γ => I.hi.toNat + waitWeight β + waitWeight γ

def waitingWeight (W : List (Formula S)) : ℕ := (W.map waitWeight).sum

noncomputable def advance (W : List (Formula S)) (t : ℕ) : List (Formula S) :=
  (update W t).flatMap waitfor

theorem waitingWeight_append (U V : List (Formula S)) :
    waitingWeight (U ++ V) = waitingWeight U + waitingWeight V := by
  simp only [waitingWeight, List.map_append, List.sum_append]

theorem waitingWeight_waitfor (φ : Formula S) : waitingWeight (waitfor φ) = waitWeight φ := by
  induction φ <;> simp_all only [waitfor, waitWeight, waitingWeight,
    List.map_append, List.sum_append, List.map_nil, List.sum_nil, List.map_cons,
    List.sum_cons, Nat.add_zero]

theorem goodWaiting_append (U V : List (Formula S)) :
    GoodWaiting (U ++ V) ↔ GoodWaiting U ∧ GoodWaiting V := by
  constructor
  · intro h
    exact ⟨fun φ hφ ↦ h φ (List.mem_append_left V hφ),
      fun φ hφ ↦ h φ (List.mem_append_right U hφ)⟩
  · rintro ⟨hU, hV⟩ φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact hU φ hφ
    · exact hV φ hφ

theorem goodWaiting_waitfor (φ : Formula S) (hφ : Bounded φ) : GoodWaiting (waitfor φ) := by
  revert hφ
  induction φ with
  | eq _ _ =>
      intro _ ψ hψ
      cases hψ
  | pred _ _ =>
      intro _ ψ hψ
      cases hψ
  | neg β ih => exact ih
  | ex x β ih => exact ih
  | prev I β ih => exact ih
  | or β γ ihβ ihγ =>
      intro hφ
      exact (goodWaiting_append _ _).mpr ⟨ihβ hφ.1, ihγ hφ.2⟩
  | since I β γ ihβ ihγ =>
      intro hφ
      exact (goodWaiting_append _ _).mpr ⟨ihβ hφ.1, ihγ hφ.2⟩
  | next I β _ =>
      intro hφ ψ hψ
      have hψ' : ψ = .next I β := List.mem_singleton.mp hψ
      subst ψ
      exact ⟨hφ, trivial⟩
  | «until» I β γ _ _ =>
      intro hφ ψ hψ
      have hψ' : ψ = .until I β γ := List.mem_singleton.mp hψ
      subst ψ
      exact ⟨hφ, trivial⟩

theorem interval_hi_toNat_pos (I : Interval) (hfinite : I.hi ≠ ⊤) : 0 < I.hi.toNat := by
  have hpositive : (0 : ℕ∞) < I.hi :=
    (show (0 : ℕ∞) ≤ (I.lo : ℕ∞) from bot_le).trans_lt I.lo_lt_hi
  exact ENat.toNat_pos (ne_of_gt hpositive) hfinite

theorem shift_bounded (I : Interval) (t : ℕ) (h : (t : ℕ∞) < I.hi)
    (hfinite : I.hi ≠ ⊤) : (I.shift t h).hi ≠ ⊤ := by
  change I.hi - (t : ℕ∞) ≠ ⊤
  rw [← ENat.natCast_toNat hfinite, ← ENat.natCast_sub]
  simp

theorem advance_append (U V : List (Formula S)) (t : ℕ) :
    advance (U ++ V) t = advance U t ++ advance V t := by
  simp only [advance, update, List.flatMap_append]

theorem advance_singleton_good (φ : Formula S) (hφ : Bounded φ) (hfuture : Future φ)
    (t : ℕ) : GoodWaiting (advance [φ] t) := by
  cases φ with
  | next I β =>
      simpa only [advance, update, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        using goodWaiting_waitfor β hφ
  | «until» I β γ =>
      by_cases ht : (t : ℕ∞) < I.hi
      · simp only [advance, update, List.flatMap_cons, List.flatMap_nil, ht, ↓reduceDIte,
          List.append_nil, waitfor]
        intro ψ hψ
        have hψ' := List.mem_singleton.mp hψ
        subst ψ
        exact ⟨⟨shift_bounded I t ht hφ.1, hφ.2⟩, trivial⟩
      · simpa only [advance, update, List.flatMap_cons, List.flatMap_nil, ht, ↓reduceDIte,
          List.append_nil] using
          (goodWaiting_append _ _).mpr
            ⟨goodWaiting_waitfor β hφ.2.1, goodWaiting_waitfor γ hφ.2.2⟩
  | _ => exact hfuture.elim

theorem advance_singleton_weight (φ : Formula S) (hφ : Bounded φ) (hfuture : Future φ)
    (t : ℕ) : waitingWeight (advance [φ] t) ≤ waitWeight φ ∧
      (0 < t → waitingWeight (advance [φ] t) < waitWeight φ) := by
  cases φ with
  | next I β =>
      simp only [advance, update, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        waitingWeight_waitfor, waitWeight]
      omega
  | «until» I β γ =>
      have hpositive := interval_hi_toNat_pos I hφ.1
      by_cases ht : (t : ℕ∞) < I.hi
      · have hshift : (I.shift t ht).hi.toNat = I.hi.toNat - t := by
          simp only [Interval.shift,
            ENat.toNat_sub (n := (t : ℕ∞)) (by simp), ENat.toNat_natCast]
        simp only [advance, update, List.flatMap_cons, List.flatMap_nil, ht, ↓reduceDIte,
          List.append_nil, waitfor, waitingWeight, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, waitWeight, hshift]
        omega
      · simp only [advance, update, List.flatMap_cons, List.flatMap_nil, ht, ↓reduceDIte,
          List.append_nil, waitingWeight_append, waitingWeight_waitfor, waitWeight]
        omega
  | _ => exact hfuture.elim

theorem advance_good (W : List (Formula S)) (hW : GoodWaiting W) (t : ℕ) :
    GoodWaiting (advance W t) := by
  revert hW
  induction W with
  | nil =>
      intro _ ψ hψ
      cases hψ
  | cons φ W ih =>
      intro hW
      have hφ := hW φ List.mem_cons_self
      have htail : GoodWaiting W := fun ψ hψ ↦ hW ψ (List.mem_cons_of_mem φ hψ)
      change GoodWaiting (advance ([φ] ++ W) t)
      rw [advance_append, goodWaiting_append]
      exact ⟨advance_singleton_good φ hφ.1 hφ.2 t, ih htail⟩

theorem advance_weight (W : List (Formula S)) (hW : GoodWaiting W) (t : ℕ) :
    waitingWeight (advance W t) ≤ waitingWeight W ∧
      (0 < t → W ≠ [] → waitingWeight (advance W t) < waitingWeight W) := by
  revert hW
  induction W with
  | nil =>
      intro _
      simp only [advance, update, List.flatMap_nil, waitingWeight,
        List.map_nil, List.sum_nil, le_refl, ne_eq, not_true_eq_false, false_implies,
        implies_true, and_self]
  | cons φ W ih =>
      intro hW
      have hφ := hW φ List.mem_cons_self
      have htail : GoodWaiting W := fun ψ hψ ↦ hW ψ (List.mem_cons_of_mem φ hψ)
      have hh := advance_singleton_weight φ hφ.1 hφ.2 t
      have ht := ih htail
      have hadv : waitingWeight (advance (φ :: W) t) =
          waitingWeight (advance [φ] t) + waitingWeight (advance W t) := by
        change waitingWeight (advance ([φ] ++ W) t) = _
        rw [advance_append, waitingWeight_append]
      have hcons : waitingWeight (φ :: W) = waitWeight φ + waitingWeight W := rfl
      simp only [hadv, hcons]
      constructor
      · omega
      · intro hpositive _
        have := hh.2 hpositive
        omega

theorem bounded_of_mem_subformulas (Φ : Formula S) :
    Bounded Φ → ∀ α, α ∈ subformulas Φ → Bounded α := by
  induction Φ with
  | eq _ _ =>
      intro hΦ α hα
      have hα' := List.mem_singleton.mp hα
      subst α
      exact hΦ
  | pred _ _ =>
      intro hΦ α hα
      have hα' := List.mem_singleton.mp hα
      subst α
      exact hΦ
  | neg β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | ex x β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | prev I β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | next I β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | or β γ ihβ ihγ =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · rcases List.mem_append.mp hα with hα | hα
        · exact ihβ hΦ.1 α hα
        · exact ihγ hΦ.2 α hα
  | since I β γ ihβ ihγ =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · rcases List.mem_append.mp hα with hα | hα
        · exact ihβ hΦ.1 α hα
        · exact ihγ hΦ.2 α hα
  | «until» I β γ ihβ ihγ =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · rcases List.mem_append.mp hα with hα | hα
        · exact ihβ hΦ.2.1 α hα
        · exact ihγ hΦ.2.2 α hα

theorem bounded_of_mem_tempSubs (Φ : Formula S) (hΦ : Bounded Φ) (α : Formula S)
    (hα : α ∈ tempSubs Φ) : Bounded α :=
  bounded_of_mem_subformulas Φ hΦ α (List.mem_filter.mp hα).1

theorem run_goodWaiting (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ) (k : ℕ) :
    ∀ α j W, (α, j, W) ∈ (run D Φ k).Q → GoodWaiting W := by
  induction k with
  | zero =>
      intro α j W hmem
      obtain ⟨β, hβ, heq⟩ := List.mem_map.mp hmem
      cases heq
      exact goodWaiting_waitfor _ (bounded_of_mem_tempSubs Φ hΦ _ hβ)
  | succ k ih =>
      intro α j W hmem
      rw [run_succ, iteration_Q] at hmem
      rcases mem_updateQ_cases D Φ (run D Φ k) α j W hmem with
        ⟨U, hU, _, rfl⟩ | ⟨hα, _, rfl⟩
      · exact advance_good U (ih α j U hU) _
      · exact goodWaiting_waitfor α (bounded_of_mem_tempSubs Φ hΦ α hα)

theorem mem_next_of_nonempty (D : TempStruct S) (Φ : Formula S) (k : ℕ)
    (α : Formula S) (j : ℕ) (W : List (Formula S))
    (hmem : (α, j, W) ∈ (run D Φ k).Q) (hne : W ≠ []) :
    (α, j, advance W (D.τ (k + 1) - D.τ k)) ∈ (run D Φ (k + 1)).Q := by
  rw [run_succ, iteration_Q]
  apply List.mem_append_left
  apply List.mem_filterMap.mpr
  refine ⟨(α, j, W), hmem, ?_⟩
  have hempty : W.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [hempty, Bool.false_eq_true, ↓reduceIte, run_ell, advance]

theorem exists_progress_step (D : TempStruct S) (k : ℕ) :
    ∃ l, k ≤ l ∧ D.τ l < D.τ (l + 1) := by
  by_contra h
  have hconstant_step : ∀ l, k ≤ l → D.τ (l + 1) = D.τ l := by
    intro l hl
    have hmono := D.mono (Nat.le_succ l)
    change D.τ l ≤ D.τ (l + 1) at hmono
    have hnot : ¬ D.τ l < D.τ (l + 1) := fun hlt ↦ h ⟨l, hl, hlt⟩
    omega
  have hconstant : ∀ n, D.τ (k + n) = D.τ k := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Nat.add_succ, hconstant_step (k + n) (by omega), ih]
  obtain ⟨l, hl⟩ := D.progress (D.τ k)
  rcases le_or_gt l k with hlk | hkl
  · have := D.mono hlk
    omega
  · have heq : l = k + (l - k) := by omega
    rw [heq, hconstant] at hl
    omega

theorem pending_later_weight (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ)
    (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S))
    (hmem : (α, j, W) ∈ (run D Φ k).Q)
    (hno : ∀ l, k ≤ l → (α, j, ([] : List (Formula S))) ∉ (run D Φ l).Q) (n : ℕ) :
    ∃ V, (α, j, V) ∈ (run D Φ (k + n)).Q ∧ waitingWeight V ≤ waitingWeight W := by
  induction n with
  | zero => exact ⟨W, hmem, le_rfl⟩
  | succ n ih =>
      obtain ⟨V, hV, hweight⟩ := ih
      have hne : V ≠ [] := by
        intro heq
        subst V
        exact hno (k + n) (by omega) hV
      have hgood := run_goodWaiting D Φ hΦ (k + n) α j V hV
      refine ⟨advance V (D.τ (k + n + 1) - D.τ (k + n)), ?_, ?_⟩
      · simpa only [Nat.add_succ] using mem_next_of_nonempty D Φ (k + n) α j V hV hne
      · exact (advance_weight V hgood _).1.trans hweight

theorem observation_two (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ)
    (_huniq : TemporalSubformulasOnce Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S)),
      (α, j, W) ∈ (run D Φ k).Q →
        ∃ k', k ≤ k' ∧ (α, j, ([] : List (Formula S))) ∈ (run D Φ k').Q := by
  classical
  intro k α j W hmem
  by_contra hnot
  have hno : ∀ l, k ≤ l → (α, j, ([] : List (Formula S))) ∉ (run D Φ l).Q := by
    intro l hl hmem'
    exact hnot ⟨l, hl, hmem'⟩
  let P : ℕ → Prop := fun n ↦ ∃ l V, k ≤ l ∧ (α, j, V) ∈ (run D Φ l).Q ∧
    waitingWeight V = n
  have hex : ∃ n, P n := ⟨waitingWeight W, k, W, le_rfl, hmem, rfl⟩
  obtain ⟨l, V, hkl, hV, hweight⟩ := Nat.find_spec hex
  obtain ⟨m, hlm, hprogress⟩ := exists_progress_step D l
  have hno_l : ∀ m, l ≤ m → (α, j, ([] : List (Formula S))) ∉ (run D Φ m).Q :=
    fun m hlm ↦ hno m (hkl.trans hlm)
  obtain ⟨U, hU, hUV⟩ := pending_later_weight D Φ hΦ l α j V hV hno_l (m - l)
  have hladd : l + (m - l) = m := Nat.add_sub_of_le hlm
  rw [hladd] at hU
  have hUne : U ≠ [] := by
    intro heq
    subst U
    exact hno m (hkl.trans hlm) hU
  let U' := advance U (D.τ (m + 1) - D.τ m)
  have hU' : (α, j, U') ∈ (run D Φ (m + 1)).Q :=
    mem_next_of_nonempty D Φ m α j U hU hUne
  have hless : waitingWeight U' < waitingWeight U :=
    (advance_weight U (run_goodWaiting D Φ hΦ m α j U hU) _).2 (by omega) hUne
  have hmin := Nat.find_min' hex
    (show P (waitingWeight U') from ⟨m + 1, U', by omega, hU', rfl⟩)
  omega

end MFOTLMon.Monitor.QueueProof

open MFOTLMon.Monitor

theorem solution {S : Signature} (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ)
    (huniq : TemporalSubformulasOnce Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S)), (α, j, W) ∈ (run D Φ k).Q →
      ∃ k', k ≤ k' ∧ (α, j, ([] : List (Formula S))) ∈ (run D Φ k').Q := by
  exact QueueProof.observation_two D Φ hΦ huniq
