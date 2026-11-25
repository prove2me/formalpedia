-- Prove2me | solution 1 for GlobalTheory.Proof.TwistSupportPeriodicLevels.coords_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:50:26.626434+00:00
-- url     : https://prove2.me/submissions/7be8752d-826a-4650-be1c-ef787afa312d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.TwistSupportPeriodicLevels
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r s s' : Type} [Fintype r] [DecidableEq r]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
theorem _root_.solution (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (x y : Matrix Y Y' k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp
end GlobalTheory.Proof.TwistSupportPeriodicLevels
