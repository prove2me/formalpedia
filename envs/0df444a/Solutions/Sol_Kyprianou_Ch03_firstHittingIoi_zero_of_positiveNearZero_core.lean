-- Prove2me | solution 1 for Kyprianou.Ch03.firstHittingIoi_zero_of_positiveNearZero_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:40:58.058176+00:00
-- url     : https://prove2.me/submissions/fbd28bc4-2a52-4d49-baac-7f81ff07b9f2

import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03


theorem solution
    {Omega : Type} (X : NNReal -> Omega -> Real) (omega : Omega)
    (hXZero : X 0 omega = 0)
    (hNear : forall epsilon : NNReal, 0 < epsilon ->
      ∃ s : NNReal, s < epsilon ∧ 0 < X s omega) :
    firstHittingTime X (Set.Ioi (0 : Real)) omega = 0 := by
  unfold firstHittingTime
  let S : Set (WithTop NNReal) :=
    (fun s : NNReal => (s : WithTop NNReal)) ''
      {s : NNReal | 0 < s ∧ X s omega ∈ Set.Ioi (0 : Real)}
  change sInf S = 0
  by_contra hNonzero
  have hPos : (0 : WithTop NNReal) < sInf S :=
    lt_of_le_of_ne bot_le (Ne.symm hNonzero)
  obtain ⟨u, huPos, huSmall⟩ := exists_between hPos
  have huTop : u ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le huSmall le_top)
  obtain ⟨epsilon, rfl⟩ := WithTop.ne_top_iff_exists.mp huTop
  have hEps : (0 : NNReal) < epsilon := by
    exact_mod_cast huPos
  obtain ⟨s, hsSmall, hsAbove⟩ := hNear epsilon hEps
  have hsPos : (0 : NNReal) < s := by
    by_contra hsNonpos
    have hsZero : s = 0 :=
      le_antisymm (le_of_not_gt hsNonpos) (show (0 : NNReal) ≤ s from zero_le)
    simp [hsZero, hXZero] at hsAbove
  have hInfLe : sInf S ≤ (s : WithTop NNReal) := by
    exact sInf_le ⟨s, ⟨hsPos, hsAbove⟩, rfl⟩
  have hsLt : (s : WithTop NNReal) < (epsilon : WithTop NNReal) := by
    exact_mod_cast hsSmall
  exact (not_lt_of_ge hInfLe) (lt_trans hsLt huSmall)

