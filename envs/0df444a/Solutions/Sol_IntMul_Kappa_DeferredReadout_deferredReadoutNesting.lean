-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.deferredReadoutNesting
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T07:55:57.670221+00:00
-- url     : https://prove2.me/submissions/86aaf0ae-acb4-4d52-8000-ff47c718a0f0

import Definitions.Def_IntMul_Kappa_DeferredReadoutCertificates

namespace IntMul.Kappa.DeferredReadout

theorem row_mem (n : Nat) (table : RowTable) {B : Frame} {r : Nat} (h : r ∈ B) :
    row n table r ∈ space n table B :=
  Submodule.subset_span ⟨r, h, rfl⟩

private theorem combination_mem (n : Nat) (table : RowTable) (B : Frame)
    (terms : List (Nat × Int)) (hin : ∀ t ∈ terms, t.1 ∈ B) :
    (fun j : Fin n => (combination table terms j.val : ℚ)) ∈ space n table B := by
  induction terms with
  | nil => exact (space n table B).zero_mem
  | cons t rest ih =>
    rcases t with ⟨r, c⟩
    have hr := row_mem n table (hin (r, c) (.head _))
    have hs := ih (fun x hx => hin x (.tail _ hx))
    convert (space n table B).add_mem ((space n table B).smul_mem (c : ℚ) hr) hs using 1
    funext j
    simp [combination, row, Pi.smul_apply]

theorem identity_mem (n : Nat) (table : RowTable) {B : Frame} {e : Identity}
    (hv : validIdentity n table e = true) (hin : ∀ t ∈ e.terms, t.1 ∈ B) :
    row n table e.lhs ∈ space n table B := by
  simp only [validIdentity, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hv
  have hden : (e.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv.1)
  apply ((space n table B).smul_mem_iff hden).mp
  have eqv : (e.den : ℚ) • row n table e.lhs =
      fun j : Fin n => (combination table e.terms j.val : ℚ) := by
    funext j
    change (e.den : ℚ) * (table e.lhs j.val : ℚ) = _
    exact_mod_cast hv.2 j.val (List.mem_range.mpr j.isLt)
  rw [eqv]
  exact combination_mem n table B e.terms hin

theorem edge_sound (n : Nat) (table : RowTable) (ids : Nat → Identity)
    (A B : Frame) (refs : List Nat) (ok : edgeCheck ids A B refs = true)
    (good : ∀ i ∈ refs, validIdentity n table (ids i) = true) :
    space n table A ≤ space n table B := by
  apply Submodule.span_le.mpr
  rintro x ⟨r, hr, rfl⟩
  have h := List.all_eq_true.mp ok r hr
  have choice : r ∈ B ∨ ∃ i ∈ refs, covers ids B r i = true := by simpa using h
  rcases choice with h | ⟨i, hi, hit⟩
  · exact row_mem n table h
  ·
    simp only [covers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      List.contains_iff_mem] at hit
    rw [← hit.1]
    exact identity_mem n table (good i hi) hit.2

/-- Deferred readouts nest in time. The list may contain equal consecutive
frames or be empty. The conclusion compares every earlier and later readout. -/
theorem nesting {V : Type*} [Preorder V] (frames : List V)
    (adjacent : frames.IsChain (· ≤ ·)) : frames.Pairwise (· ≤ ·) :=
  adjacent.pairwise

private theorem get_checked {α : Type} [Inhabited α] (items : Array α) (p : α → Bool)
    (ok : items.toList.all p = true) {i : Nat} (hi : i < items.size) :
    p (items[i]?.getD default) = true := by
  have h := List.all_eq_true.mp ok items[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
  simpa [hi] using h

private theorem Block.transition_sound (d : Block) (hi : d.identitiesOK = true)
    (he : d.edgesOK = true) {a b : Event} (hab : d.transitionOK a b = true) :
    d.atEvent a ≤ d.atEvent b := by
  simp [transitionOK] at hab
  rcases hab with same | ⟨⟨bound, src⟩, dst⟩
  · simp [atEvent, same]
  · let e := d.edge a.edge
    have ok : d.edgeOK e = true := get_checked d.edges d.edgeOK he bound
    simp only [edgeOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ok
    have le := edge_sound 23 d.entry d.identity (d.basis e.first) (d.basis e.second) e.refs
      ok.2 (fun i h => get_checked d.ids (validIdentity 23 d.entry) hi (ok.1 i h))
    change space 23 d.entry (d.basis a.frame) ≤ space 23 d.entry (d.basis b.frame)
    rwa [← src, ← dst]

private theorem Block.chain_of_timeline (d : Block) (hi : d.identitiesOK = true)
    (he : d.edgesOK = true) : ∀ es : List Event, d.timelineOK es = true →
    (es.map d.atEvent).IsChain (· ≤ ·)
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: rest, ok => by
    have both := Bool.and_eq_true_iff.mp ok
    have lt := d.transition_sound hi he both.1
    have ih := d.chain_of_timeline hi he (b :: rest) both.2
    simpa only [List.map_cons, List.isChain_cons_cons] using And.intro lt ih

/-- Every earlier readout frame lies in each later one for every target of a
checked block. The hypotheses are finite equalities on the published data. -/
private theorem checked_nesting (d : Block) (hi : d.identitiesOK = true)
    (he : d.edgesOK = true) (ht : d.timelinesOK = true) (t : Fin d.targets.size) :
    (d.targets[t.val].map d.atEvent).Pairwise (· ≤ ·) := by
  apply nesting
  apply d.chain_of_timeline hi he
  apply List.all_eq_true.mp ht
  exact Array.mem_toList_iff.mpr (Array.getElem_mem t.isLt)

end IntMul.Kappa.DeferredReadout

open IntMul.Kappa.DeferredReadout

theorem solution (d : Block) (hi : d.identitiesOK = true)
    (he : d.edgesOK = true) (ht : d.timelinesOK = true) (t : Fin d.targets.size) :
    (d.targets[t.val].map d.atEvent).Pairwise (· ≤ ·) :=
  checked_nesting d hi he ht t
