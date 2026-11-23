-- Prove2me | solution 1 for LinuxRV.monitor_correct
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T08:58:25.342092+00:00
-- url     : https://prove2.me/submissions/7db5b731-3dc7-44c1-8b34-f85d3c50f0d6

import Definitions.Def_LinuxRV_TransitionTable
open RamadgeWonham.Shared

namespace LRMon
open LinuxRV

theorem cell {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) (q : G.Q) (e : α) :
    (compileTable G states events)[states q][events e] = encodeNext states (G.δ e q) := by
  simp [compileTable]

theorem decode_encode {σ : Type} {n : Nat} (states : σ ≃ Fin n) (x : Option σ) :
    decodeCell (n := n) (encodeNext states x) = x.map states := by
  cases x with
  | none => simp [encodeNext, decodeCell]
  | some q =>
    have he : encodeNext states (some q) = ((states q).val : Int) := rfl
    rw [he, Option.map_some]
    unfold decodeCell
    rw [dif_pos ⟨by omega, by simp⟩]
    simp

theorem foldl_none {α : Type} (G : Generator α) (s : List α) :
    s.foldl (fun o σ => o.bind (G.δ σ)) (none : Option G.Q) = none := by
  induction s with
  | nil => rfl
  | cons a s ih => simpa using ih

theorem runFrom_nil {α : Type} (G : Generator α) (q : G.Q) : G.runFrom q [] = some q := rfl

theorem runFrom_cons {α : Type} (G : Generator α) (q : G.Q) (a : α) (s : List α) :
    G.runFrom q (a :: s) = (match G.δ a q with
      | none => none
      | some q' => G.runFrom q' s) := by
  unfold Generator.runFrom
  cases h : G.δ a q with
  | none => simp [h, foldl_none]
  | some q' => simp [h]

theorem main {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) (trace : List α) :
    ∀ (q : G.Q) (off : Nat),
    (∀ q', scan (compileTable G states events) (states q) off (trace.map events) = .ok (states q')
        ↔ G.runFrom q trace = some q') ∧
    (∀ i q1 e, scan (compileTable G states events) (states q) off (trace.map events)
        = .error (i, states q1, events e) ↔
      ∃ pre post, trace = pre ++ e :: post ∧ off + pre.length = i ∧
        G.runFrom q pre = some q1 ∧ G.δ e q1 = none) := by
  induction trace with
  | nil =>
    intro q off
    refine ⟨fun q' => ?_, fun i q1 e => ?_⟩
    · simp [scan, runFrom_nil]
    · simp [scan]
  | cons a rest ih =>
    intro q off
    have hs : scan (compileTable G states events) (states q) off ((a :: rest).map events) =
        (match (G.δ a q).map states with
          | none => .error (off, states q, events a)
          | some next => scan (compileTable G states events) next (off + 1) (rest.map events)) := by
      rw [List.map_cons, scan, cell, decode_encode]; rfl
    rw [hs, runFrom_cons]
    cases h : G.δ a q with
    | none =>
      refine ⟨fun q' => ?_, fun i q1 e => ?_⟩
      · simp
      · simp only [Option.map_none, Except.error.injEq, Prod.mk.injEq,
          EmbeddingLike.apply_eq_iff_eq]
        constructor
        · rintro ⟨rfl, rfl, rfl⟩
          exact ⟨[], rest, rfl, by simp, rfl, h⟩
        · rintro ⟨pre, post, hpre, hlen, hrun, hδ⟩
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hpre
            obtain ⟨rfl, -⟩ := hpre
            simp only [runFrom_nil, Option.some.injEq] at hrun
            subst hrun
            simp at hlen
            exact ⟨hlen, rfl, rfl⟩
          | cons b pre' =>
            simp only [List.cons_append, List.cons.injEq] at hpre
            obtain ⟨rfl, -⟩ := hpre
            rw [runFrom_cons, h] at hrun
            simp at hrun
    | some q' =>
      obtain ⟨ih1, ih2⟩ := ih q' (off + 1)
      refine ⟨fun q'' => ?_, fun i q1 e => ?_⟩
      · simpa using ih1 q''
      · simp only [Option.map_some]
        rw [ih2]
        constructor
        · rintro ⟨pre, post, hpre, hlen, hrun, hδ⟩
          refine ⟨a :: pre, post, by simp [hpre], by simp; omega, ?_, hδ⟩
          rw [runFrom_cons, h]; exact hrun
        · rintro ⟨pre, post, hpre, hlen, hrun, hδ⟩
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hpre
            obtain ⟨rfl, -⟩ := hpre
            simp only [runFrom_nil, Option.some.injEq] at hrun
            subst hrun
            rw [h] at hδ; exact absurd hδ (by simp)
          | cons b pre' =>
            simp only [List.cons_append, List.cons.injEq] at hpre
            obtain ⟨rfl, hrest⟩ := hpre
            rw [runFrom_cons, h] at hrun
            refine ⟨pre', post, hrest, by simp at hlen; omega, hrun, hδ⟩

end LRMon

open LinuxRV in
theorem solution {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) (trace : List α) :
    (∀ q, monitor G states events trace = .ok (states q) ↔ G.run trace = some q) ∧
    (∀ i q e, monitor G states events trace = .error (i, states q, events e) ↔
      ∃ pre post, trace = pre ++ e :: post ∧ pre.length = i ∧
        G.run pre = some q ∧ G.δ e q = none) := by
  obtain ⟨h1, h2⟩ := LRMon.main G states events trace G.q0 0
  refine ⟨fun q => h1 q, fun i q e => ?_⟩
  unfold monitor
  rw [h2]
  simp [Generator.run]
