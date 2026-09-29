-- Prove2me | solution 1 for KServer.chunk_size_le_price
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-10T10:26:53.177618+00:00
-- url     : https://prove2.me/submissions/ae0a662f-eed8-4ac7-b73e-dea8387eef38

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

open KServer


/-!
# The size of a chunk never exceeds the escape price

The escape rule that bails immediately shows that every nonempty chunk of a chunk system with
online escapes has size at most the escape price.
-/



namespace SizePrice

variable {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ} {mL : ℕ}

open Classical in
/-- A crude evader: it jumps into an arbitrary point of the last request. -/
noncomputable def anyPos (b : X) (l : List (Set X)) : X :=
  match l.getLast? with
  | none => b
  | some S => if h : S.Nonempty then h.choose else b

open Classical in
theorem anyPos_serves (b : X) (l : List (Set X)) (S : Set X) (hS : S.Nonempty) :
    anyPos b (l ++ [S]) ∈ S := by
  have hlast : (l ++ [S]).getLast? = some S := by simp
  unfold anyPos
  rw [hlast]
  show (if h : S.Nonempty then h.choose else b) ∈ S
  rw [dif_pos hS]
  exact hS.choose_spec

/-- The crude evader as an `EvaderAlgorithm`. -/
noncomputable def anyEvader (b : X) : EvaderAlgorithm X where
  pos := anyPos b
  serves := anyPos_serves b

theorem bailTime_always {Y : Type*} (h χ : List (Set Y)) (hχ : χ ≠ []) :
    bailTime (fun _ => true) h χ = some 0 := by
  unfold bailTime
  obtain ⟨n, hn⟩ : ∃ n, χ.length = n + 1 := by
    cases χ with
    | nil => exact absurd rfl hχ
    | cons a l => exact ⟨l.length, by simp⟩
  rw [hn, List.range_succ_eq_map]
  simp

/-- **Every chunk has size at most the escape price** (assuming the price is nonnegative). -/
theorem size_le_price (C : ChunkSystemB X s t cLo cHi total price mL) (hp : 0 ≤ price)
    (ω : C.Ω) (i : Fin C.m) : C.size ω i ≤ price := by
  classical
  set E : EvaderAlgorithm X := anyEvader t with hE
  have hc := C.hcost i ω E (fun _ => true)
  have hle : ∀ ω' : C.Ω,
      E.bailCost (fun _ => true) (((List.ofFn (C.chunk ω')).take i).flatten)
        (C.chunk ω' i) price ≤ price := by
    intro ω'
    by_cases h : C.chunk ω' i = []
    · unfold EvaderAlgorithm.bailCost bailTime
      rw [h]
      simpa [EvaderAlgorithm.costOn] using hp
    · unfold EvaderAlgorithm.bailCost
      rw [bailTime_always _ _ h]
      show E.costOn _ ((C.chunk ω' i).take 0) + price ≤ price
      simp [EvaderAlgorithm.costOn]
  set A : Finset C.Ω := Finset.univ.filter (fun ω' => C.hist i ω' = C.hist i ω) with hA
  have hmass : 0 < ∑ ω' ∈ A, C.P ω' := by
    refine Finset.sum_pos' (fun ω' _ => le_of_lt (C.hP ω')) ⟨ω, ?_, C.hP ω⟩
    rw [hA]
    simp
  have hR : ∑ ω' ∈ A, C.P ω' *
      E.bailCost (fun _ => true) (((List.ofFn (C.chunk ω')).take i).flatten)
        (C.chunk ω' i) price ≤ price * ∑ ω' ∈ A, C.P ω' := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ω' _ => ?_
    rw [mul_comm price (C.P ω')]
    exact mul_le_mul_of_nonneg_left (hle ω') (le_of_lt (C.hP ω'))
  have hfin : C.size ω i * ∑ ω' ∈ A, C.P ω' ≤ price * ∑ ω' ∈ A, C.P ω' :=
    le_trans hc hR
  exact le_of_mul_le_mul_right (by linarith [hfin]) hmass

end SizePrice


theorem solution {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mL) (hp : 0 ≤ price)
    (ω : C.Ω) (i : Fin C.m) : C.size ω i ≤ price :=
  SizePrice.size_le_price C hp ω i
