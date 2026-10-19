-- Prove2me | solution 2 for OAI.Problem356.FiniteCells.cellLabel_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:35:55.710824+00:00
-- url     : https://prove2.me/submissions/ae16c0b0-c01d-46b4-ad79-4b8062d9ab6a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/PartitionLabel.lean:L24-L40
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.FiniteCells.cellLabel_eq_some_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.CoulombTransport.PartitionLabel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uX uIndex

noncomputable section

open Set MeasureTheory

namespace Problem356.FiniteCells

lemma cellLabel_eq_some_iff {X : Type uX} {ι : Type uIndex} {A : ι → Set X}
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (x : X) (i : ι) :
    cellLabel A x = some i ↔ x ∈ A i := by
  classical
  unfold cellLabel
  split_ifs with h
  · constructor
    · intro hi
      have hi' := Option.some.inj hi
      rw [← hi']
      exact Classical.choose_spec h
    · intro hx
      congr 1
      by_contra hne
      exact Set.disjoint_left.mp (hDisjoint hne) (Classical.choose_spec h) hx
  · have hi : x ∉ A i := fun hx => h ⟨i, hx⟩
    simp [hi]

end Problem356.FiniteCells

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.FiniteCells
open Set MeasureTheory


theorem solution.{uX,uIndex} : type_of% @_root_.OAI.Problem356.FiniteCells.cellLabel_eq_some_iff.{uX,uIndex} := @_root_.OAI.Problem356.FiniteCells.cellLabel_eq_some_iff.{uX,uIndex}
