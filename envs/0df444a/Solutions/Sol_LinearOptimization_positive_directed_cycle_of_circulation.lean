-- Prove2me | solution 1 for LinearOptimization.positive_directed_cycle_of_circulation
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T16:06:03.13432+00:00
-- url     : https://prove2.me/submissions/62a4e5ad-b8e0-49b4-9665-f272b0b00971

import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic

open Matrix

namespace LinearOptimization

private lemma circulation_balance {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (f : Fin m → ℝ)
    (hcirc : IsCirculation arcs f) (v : Fin n) :
    (∑ e, if (arcs e).1 = v then f e else 0) =
      ∑ e, if (arcs e).2 = v then f e else 0 := by
  have hv := congrFun hcirc v
  simp only [IsCirculation, Matrix.mulVec, dotProduct, incidenceMatrix,
    Matrix.of_apply, Pi.zero_apply] at hv
  simp_rw [sub_mul] at hv
  rw [Finset.sum_sub_distrib] at hv
  simp_rw [ite_mul, one_mul, zero_mul] at hv
  linarith

private lemma positive_outgoing_from_positive_incoming {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (f : Fin m → ℝ)
    (hnn : 0 ≤ f) (hcirc : IsCirculation arcs f)
    (e : Fin m) (he : 0 < f e) :
    ∃ e' : Fin m, (arcs e').1 = (arcs e).2 ∧ 0 < f e' := by
  let v := (arcs e).2
  have hin_nonneg : ∀ e' : Fin m,
      0 ≤ if (arcs e').2 = v then f e' else 0 := by
    intro e'
    split
    · exact hnn e'
    · exact le_rfl
  have hin_pos : 0 < ∑ e', if (arcs e').2 = v then f e' else 0 := by
    apply Finset.sum_pos'
    · intro e' _
      exact hin_nonneg e'
    · refine ⟨e, Finset.mem_univ _, ?_⟩
      simpa [v] using he
  have hout_pos : 0 < ∑ e', if (arcs e').1 = v then f e' else 0 := by
    rw [circulation_balance arcs f hcirc v]
    exact hin_pos
  by_contra hnone
  push_neg at hnone
  have hzero : ∀ e' : Fin m,
      (if (arcs e').1 = v then f e' else 0) = 0 := by
    intro e'
    by_cases htail : (arcs e').1 = v
    · simp only [htail, ↓reduceIte]
      exact le_antisymm (hnone e' htail) (hnn e')
    · simp [htail]
  simp_rw [hzero] at hout_pos
  simp at hout_pos

private lemma isWalkFrom_ofFn_forward {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (edge : ℕ → Fin m)
    (hlink : ∀ r, (arcs (edge r)).2 = (arcs (edge (r + 1))).1)
    (p d : ℕ) :
    IsWalkFrom arcs (arcs (edge p)).1 (arcs (edge (p + d))).1
      (List.ofFn fun a : Fin d => (edge (p + a), true)) := by
  induction d generalizing p with
  | zero => simp [IsWalkFrom]
  | succ d ih =>
      rw [List.ofFn_succ]
      simp only [IsWalkFrom]
      constructor
      · simp [stepStart]
      · simp only [stepEnd, if_pos rfl, Fin.val_zero, Nat.add_zero]
        rw [hlink p]
        simpa [Fin.succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (ih (p + 1))

end LinearOptimization

theorem solution {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (hloop : LinearOptimization.HasNoSelfLoops arcs) (f : Fin m → ℝ)
    (hnn : 0 ≤ f) (hcirc : LinearOptimization.IsCirculation arcs f)
    (hne : f ≠ 0) :
    ∃ (v : Fin n) (steps : List (Fin m × Bool)),
      LinearOptimization.IsCycle arcs v steps ∧
      (∀ st ∈ steps, st.2 = true) ∧
      ∀ st ∈ steps, 0 < f st.1 := by
  classical
  have hex_pos : ∃ e : Fin m, 0 < f e := by
    by_contra h
    push_neg at h
    apply hne
    funext e
    exact le_antisymm (h e) (hnn e)
  let PosEdge := {e : Fin m // 0 < f e}
  let e₀ : PosEdge := ⟨Classical.choose hex_pos, Classical.choose_spec hex_pos⟩
  let next : PosEdge → PosEdge := fun e =>
    ⟨Classical.choose
        (LinearOptimization.positive_outgoing_from_positive_incoming
          arcs f hnn hcirc e.1 e.2),
      (Classical.choose_spec
        (LinearOptimization.positive_outgoing_from_positive_incoming
          arcs f hnn hcirc e.1 e.2)).2⟩
  have hnext (e : PosEdge) :
      (arcs (next e).1).1 = (arcs e.1).2 :=
    (Classical.choose_spec
      (LinearOptimization.positive_outgoing_from_positive_incoming
        arcs f hnn hcirc e.1 e.2)).1
  let es : ℕ → PosEdge := fun r => (next^[r]) e₀
  have hes_succ (r : ℕ) : es (r + 1) = next (es r) := by
    simp [es, Function.iterate_succ_apply']
  have hlink (r : ℕ) :
      (arcs (es r).1).2 = (arcs (es (r + 1)).1).1 := by
    rw [hes_succ]
    exact (hnext (es r)).symm
  let vs : ℕ → Fin n := fun r => (arcs (es r).1).1
  obtain ⟨i, j, hij, hvij⟩ :=
    Finite.exists_ne_map_eq_of_infinite vs
  have hperiod_exists :
      ∃ d : ℕ, 0 < d ∧ ∃ p : ℕ, vs p = vs (p + d) := by
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · refine ⟨j - i, by omega, i, ?_⟩
      simpa [Nat.add_sub_of_le hijlt.le] using hvij
    · refine ⟨i - j, by omega, j, ?_⟩
      simpa [Nat.add_sub_of_le hjilt.le] using hvij.symm
  let d := Nat.find hperiod_exists
  have hd_spec : 0 < d ∧ ∃ p : ℕ, vs p = vs (p + d) :=
    Nat.find_spec hperiod_exists
  have hd_pos : 0 < d := hd_spec.1
  obtain ⟨p, hperiod⟩ := hd_spec.2
  have hvs_inj : Function.Injective (fun a : Fin d => vs (p + a)) := by
    intro a b hab
    apply Fin.ext
    by_contra habne
    rcases lt_or_gt_of_ne habne with halt | hblt
    · have hsmall : b.val - a.val < d := by omega
      have hshort : 0 < b.val - a.val ∧
          ∃ q : ℕ, vs q = vs (q + (b.val - a.val)) := by
        refine ⟨by omega, p + a.val, ?_⟩
        have hidx : p + a.val + (b.val - a.val) = p + b.val := by omega
        simpa [hidx] using hab
      exact (Nat.find_min hperiod_exists hsmall) hshort
    · have hsmall : a.val - b.val < d := by omega
      have hshort : 0 < a.val - b.val ∧
          ∃ q : ℕ, vs q = vs (q + (a.val - b.val)) := by
        refine ⟨by omega, p + b.val, ?_⟩
        have hidx : p + b.val + (a.val - b.val) = p + a.val := by omega
        simpa [hidx] using hab.symm
      exact (Nat.find_min hperiod_exists hsmall) hshort
  let steps : List (Fin m × Bool) :=
    List.ofFn fun a : Fin d => ((es (p + a)).1, true)
  refine ⟨vs p, steps, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro hnil
      have : steps.length = 0 := by simp [hnil]
      simp [steps, hd_pos.ne'] at this
    · have hw := LinearOptimization.isWalkFrom_ofFn_forward
        arcs (fun r => (es r).1) hlink p d
      change LinearOptimization.IsWalkFrom arcs (vs p) (vs p) steps
      change LinearOptimization.IsWalkFrom arcs (vs p) (vs (p + d)) steps at hw
      simpa only [hperiod] using hw
    · have hnodes :
          LinearOptimization.walkNodes arcs (vs p) steps =
            List.ofFn (fun a : Fin (d + 1) => vs (p + a)) := by
        simp only [LinearOptimization.walkNodes, steps, vs, List.map_ofFn,
          Function.comp_apply, LinearOptimization.stepEnd, if_pos rfl]
        rw [List.ofFn_succ]
        congr 1
        apply List.ofFn_inj.mpr
        funext a
        simp only [Function.comp_apply, LinearOptimization.stepEnd, if_pos rfl]
        rw [hlink]
        congr 3
      rw [hnodes, List.ofFn_succ']
      simp only [List.concat_eq_append, List.dropLast_concat]
      simpa using (List.nodup_ofFn.mpr hvs_inj)
    · simp only [steps, List.map_ofFn]
      apply List.nodup_ofFn.mpr
      intro a b hab
      apply hvs_inj
      change vs (p + a) = vs (p + b)
      simp only [vs]
      change (es (p + a)).1 = (es (p + b)).1 at hab
      rw [hab]
  · intro st hst
    simp only [steps, List.mem_ofFn] at hst
    rcases hst with ⟨a, rfl⟩
    rfl
  · intro st hst
    simp only [steps, List.mem_ofFn] at hst
    rcases hst with ⟨a, rfl⟩
    exact (es (p + a)).2
