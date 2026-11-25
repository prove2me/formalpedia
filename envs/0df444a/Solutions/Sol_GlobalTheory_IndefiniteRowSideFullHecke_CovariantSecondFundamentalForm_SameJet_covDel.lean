-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.SameJet.covDel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:56:16.226797+00:00
-- url     : https://prove2.me/submissions/e2192325-3c73-482c-8774-c1a754a44713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantSecondFundamentalForm_SameJet_val
import Theorems.Thm_GlobalTheory_del_eq_of_hasFDerivAt


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
theorem _root_.solution [Fintype k] [DecidableEq k] (h : SameJet u u' z) (K : V → Matrix k k ℂ)
    (ξ : V) : covDel K u z ξ = covDel K u' z ξ := by
  rw [HermFrame.covDel, HermFrame.covDel, h.val]
  congr 1
  funext a
  obtain ⟨-, D, h1, h2⟩ := h a
  rw [del_eq_of_hasFDerivAt h1, del_eq_of_hasFDerivAt h2]
end SameJet
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
