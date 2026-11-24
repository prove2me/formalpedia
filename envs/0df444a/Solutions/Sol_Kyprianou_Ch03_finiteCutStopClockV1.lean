-- Prove2me | solution 1 for Kyprianou.Ch03.finiteCutStopClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:02:26.515642+00:00
-- url     : https://prove2.me/submissions/bbd53a34-0e6f-4dbe-b17e-4eacb6601e34

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (tauFinite : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (tauFinite w : WithTop NNReal))
    (A : Set Omega)
    (hA : ∀ t : NNReal, MeasurableSet[F t] (A ∩ {w | tau w ≤ (t : WithTop NNReal)}))
    (n : NNReal)
    : ∃ (rho : Omega → NNReal)
      (hStop : IsStoppingTime F (fun w => (rho w : WithTop NNReal))),
      (∀ w, rho w ≤ n) ∧
      MeasurableSet[hStop.measurableSpace] (A ∩ {w | tau w ≤ (n : WithTop NNReal)}) ∧
      (∀ w ∈ A ∩ {w | tau w ≤ (n : WithTop NNReal)}, rho w = tauFinite w) := by
  classical
  let rho : Omega → NNReal := fun w => if tau w ≤ (n : WithTop NNReal) then tauFinite w else n
  have heq (w : Omega) : (rho w : WithTop NNReal) = min (tau w) (n : WithTop NNReal) := by
    dsimp only [rho]
    by_cases h : tau w ≤ (n : WithTop NNReal)
    · rw [if_pos h, min_eq_left h, hFinite w (ne_top_of_le_ne_top WithTop.coe_ne_top h)]
    · rw [if_neg h, min_eq_right (le_of_not_ge h)]
  have he : (fun w => (rho w : WithTop NNReal)) = fun w => min (tau w) (n : WithTop NNReal) :=
    funext heq
  have hs : IsStoppingTime F (fun w => (rho w : WithTop NNReal)) := by
    rw [he]
    exact hTau.min_const n
  refine ⟨rho, hs, fun w => ?_, ?_, fun w hw => ?_⟩
  · apply WithTop.coe_le_coe.mp
    rw [heq w]
    exact min_le_right _ _
  · apply (hs.measurableSet _).mpr
    refine ⟨(le_iSup (fun t : NNReal => F t) n) _ (hA n), ?_⟩
    intro t
    by_cases ht : n ≤ t
    · have hset : {w | (rho w : WithTop NNReal) ≤ (t : WithTop NNReal)} = Set.univ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, heq]
        exact (min_le_right _ _).trans (WithTop.coe_le_coe.mpr ht)
      rw [hset, Set.inter_univ]
      exact F.mono ht _ (hA n)
    · have hset : (A ∩ {w | tau w ≤ (n : WithTop NNReal)}) ∩
          {w | (rho w : WithTop NNReal) ≤ (t : WithTop NNReal)} =
          A ∩ {w | tau w ≤ (t : WithTop NNReal)} := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, heq, min_le_iff, WithTop.coe_le_coe, ht, or_false]
        exact ⟨fun h => ⟨h.1.1,h.2⟩, fun h => ⟨⟨h.1,h.2.trans (WithTop.coe_le_coe.mpr (le_of_not_ge ht))⟩,h.2⟩⟩
      rw [hset]
      exact hA t
  · exact if_pos (show tau w ≤ (n : WithTop NNReal) from hw.2)
