-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:10.799163+00:00
-- url     : https://prove2.me/submissions/3f40ac29-4d5c-4a56-973d-86d2b2a69ce8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantSecondFundamentalForm_mContDiffAt_orthLift
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_mContDiffAt
import Theorems.Thm_GlobalTheory_HermFrame_extForm_eq_neg_mdbar
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
variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}
variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz
namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
theorem _root_.solution (ξ : V) : MContDiffAt ∞ (fun x => extForm H x ξ) z := by
  have hl := mContDiffAt_orthLift (h.mContDiffAt hz) (hs z hz)
  simp only [extForm_eq_neg_mdbar]
  have hc : MContDiffAt ∞ (fun x => orthCoeff (H x)) z := fun a b => by
    simpa [orthLift] using hl.neg (.inl a) b
  exact (hc.mdbar le_rfl ξ).neg
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
