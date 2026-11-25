-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.SameJet.secDbar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:33.83639+00:00
-- url     : https://prove2.me/submissions/8236f871-dfcf-4518-945e-346df907e7a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
import Theorems.Thm_GlobalTheory_dbar_eq_of_hasFDerivAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
namespace SameJet
theorem _root_.solution (h : SameJet u u' z) (ξ : V) :
    HermitianCurvatureForms.secDbar u z ξ = HermitianCurvatureForms.secDbar u' z ξ := by
  funext a
  obtain ⟨-, D, h1, h2⟩ := h a
  rw [HermitianCurvatureForms.secDbar, HermitianCurvatureForms.secDbar, dbar_eq_of_hasFDerivAt h1, dbar_eq_of_hasFDerivAt h2]
end SameJet
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
