-- Prove2me | solution 1 for Kyprianou.Ch01.branchingInverseRecoveryFromStrictClock
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:05:20.419618+00:00
-- url     : https://prove2.me/submissions/487d10e3-6e23-4982-843b-2a67cea7ad29

import Mathlib.Data.NNReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (horizon t : ℝ≥0) (ht : t < horizon)
    (hmono : Monotone (fun s : ℝ≥0 => branchingOccupation Y s ω))
    (hstrict : ∀ s : ℝ≥0, t < s → s < horizon →
      branchingOccupation Y t ω < branchingOccupation Y s ω)
    (hnonneg : 0 ≤ branchingOccupation Y t ω) :
    branchingToPoisson Y
      (Real.toNNReal (branchingOccupation Y t ω)) ω = Y t ω := by
  set J := fun s : ℝ≥0 => branchingOccupation Y s ω with hJ
  have hc : ((Real.toNNReal (branchingOccupation Y t ω) : ℝ≥0) : ℝ) = branchingOccupation Y t ω :=
    Real.coe_toNNReal _ hnonneg
  obtain ⟨m, hm1, hm2⟩ := exists_between ht
  have hS : {s : ℝ≥0 | ((Real.toNNReal (branchingOccupation Y t ω) : ℝ≥0) : ℝ) <
      branchingOccupation Y s ω} = {s : ℝ≥0 | J t < J s} := by
    ext s; simp only [Set.mem_ofPred_eq, hc, hJ]
  have hinf : sInf {s : ℝ≥0 | J t < J s} = t := by
    apply le_antisymm
    · apply le_of_forall_gt_imp_ge_of_dense
      intro a ha
      rcases lt_or_ge a horizon with h | h
      · exact csInf_le (OrderBot.bddBelow {s : ℝ≥0 | J t < J s})
          (show a ∈ {s : ℝ≥0 | J t < J s} from hstrict a ha h)
      · exact le_trans (csInf_le (OrderBot.bddBelow {s : ℝ≥0 | J t < J s})
          (show m ∈ {s : ℝ≥0 | J t < J s} from hstrict m hm1 hm2)) (le_trans hm2.le h)
    · apply le_csInf ⟨m, hstrict m hm1 hm2⟩
      intro s hs
      by_contra hlt0
      have hlt := not_le.mp hlt0
      exact absurd (hmono hlt.le) (not_le.mpr hs)
  have hex : ∃ s : ℝ≥0, ((Real.toNNReal (branchingOccupation Y t ω) : ℝ≥0) : ℝ) <
      branchingOccupation Y s ω := ⟨m, by rw [hc]; exact hstrict m hm1 hm2⟩
  have hinv : inverseBranchingOccupation Y (Real.toNNReal (branchingOccupation Y t ω)) ω =
      ((t : ℝ≥0) : WithTop ℝ≥0) := by
    unfold inverseBranchingOccupation
    simp only [hex, if_true]
    rw [hS, hinf]
  unfold branchingToPoisson
  rw [hinv]
