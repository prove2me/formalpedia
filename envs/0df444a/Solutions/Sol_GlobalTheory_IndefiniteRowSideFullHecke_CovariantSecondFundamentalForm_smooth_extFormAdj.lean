-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:44.993583+00:00
-- url     : https://prove2.me/submissions/9b20696d-b2c5-440c-864b-6db4737cb7df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantSecondFundamentalForm_smooth_extForm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_mContDiffAt
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_quot
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_sub
import Theorems.Thm_GlobalTheory_HermFrame_IsPosFrame_quot
import Theorems.Thm_GlobalTheory_HermFrame_IsPosFrame_sub
import Theorems.Thm_GlobalTheory_HermFrame_MContDiffAt_conjTranspose


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
variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz
namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
theorem _root_.solution (ξ : V) : MContDiffAt ∞ (fun x => extFormAdj H x ξ) z :=
  ((((h.quot hs).mContDiffAt hz).transpose.inv
    (by rw [det_transpose]; exact (h.quot hs).isUnit z hz)).mul
    (smooth_extForm h hs hz ξ).conjTranspose).mul ((h.sub hs).mContDiffAt hz).transpose
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
