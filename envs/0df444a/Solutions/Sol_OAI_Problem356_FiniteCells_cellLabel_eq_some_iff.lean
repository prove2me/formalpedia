-- Prove2me | solution 1 for OAI.Problem356.FiniteCells.cellLabel_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:12:27.263455+00:00
-- url     : https://prove2.me/submissions/2fb922d1-ead9-4fa7-8867-be812c5b6cf4

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel

open OAI OAI.Problem356 OAI.Problem356.FiniteCells
universe uX uIndex
open Set MeasureTheory


theorem solution {X : Type uX} {ι : Type uIndex} {A : ι → Set X}
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (x : X) (i : ι) :
    cellLabel A x = some i ↔ x ∈ A i := by
  unfold cellLabel
  by_cases h : ∃ j, x ∈ A j
  · rw [dif_pos h]
    have hc := Classical.choose_spec h
    constructor
    · intro e; cases e; exact hc
    · intro hx
      by_contra hne
      have hne' : Classical.choose h ≠ i := fun e => hne (by rw [e])
      exact Set.disjoint_left.mp (hDisjoint hne') hc hx
  · rw [dif_neg h]
    simp only [reduceCtorEq, false_iff]
    exact fun hx => h ⟨i, hx⟩

