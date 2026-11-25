-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.SameJet.mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:56:17.473581+00:00
-- url     : https://prove2.me/submissions/be22f2c8-5fef-45fc-8d58-1ccdd0251c14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
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
theorem _root_.solution [Fintype k] {p : Type*} {M : V → Matrix p k ℂ} (hM : MContDiffAt 1 M z)
    (h : SameJet u u' z) : SameJet (fun x => M x *ᵥ u x) (fun x => M x *ᵥ u' x) z := fun a => by
  choose e D h1 h2 using h
  refine ⟨by simp [Matrix.mulVec, dotProduct, e],
    ∑ b, (M z a b • D b + u' z b • fderiv ℝ (fun x => M x a b) z), ?_, ?_⟩
  · simp only [← e]
    exact HasFDerivAt.fun_sum fun b _ => (hM.diff a b).hasFDerivAt.mul (h1 b)
  · exact HasFDerivAt.fun_sum fun b _ => (hM.diff a b).hasFDerivAt.mul (h2 b)
end SameJet
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
