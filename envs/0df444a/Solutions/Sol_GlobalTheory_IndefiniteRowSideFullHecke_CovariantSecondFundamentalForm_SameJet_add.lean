-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.SameJet.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:54:53.067861+00:00
-- url     : https://prove2.me/submissions/1b436c79-e5c3-4f2b-81a8-d30cdf044a30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_IsPshC2On_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l n : Type*} [Fintype m] [Fintype l] [Fintype n]
  [DecidableEq m] [DecidableEq l] [DecidableEq n]
variable {k : Type*} {u u' v v' : V → k → ℂ} {z : V}
omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
namespace SameJet
theorem _root_.solution (h : SameJet u u' z) (h' : SameJet v v' z) :
    SameJet (fun x => u x + v x) (fun x => u' x + v' x) z := fun a => by
  obtain ⟨e, D, h1, h2⟩ := h a
  obtain ⟨e', D', h1', h2'⟩ := h' a
  exact ⟨by simp [e, e'], D + D', h1.add h1', h2.add h2'⟩
end SameJet
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
