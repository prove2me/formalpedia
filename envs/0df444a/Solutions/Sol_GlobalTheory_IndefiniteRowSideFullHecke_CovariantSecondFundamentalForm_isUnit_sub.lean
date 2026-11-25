-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.isUnit_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:39.622701+00:00
-- url     : https://prove2.me/submissions/031aed33-a8a4-471f-b2e1-7a05436bcb63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_sub
import Theorems.Thm_GlobalTheory_HermFrame_IsPosFrame_sub


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
variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}
omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
theorem _root_.solution (h : IsPosFrame U H) (z : V) (hz : z ∈ U) : IsUnit (subGram (H z)).det :=
  h.sub.isHermFrame.isUnit z hz
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
