-- Prove2me | solution 1 for GlobalTheory.SymCompare.stdOrd_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:09.128552+00:00
-- url     : https://prove2.me/submissions/35b27771-de91-40f4-a8ce-f4d953c6f9d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t t' : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype t'] [DecidableEq t']
namespace GlobalTheory.SymCompare
theorem _root_.solution (κ : Type*) {t t' : Type*} (f : t ≃ t') {l : ℕ} (j c : ℕ) (h : j + c = l) :
    (eI (κ ⊕ Fin l) f j).trans (stdOrd κ t' j c h) = (stdOrd κ t j c h).trans (sE (eI (κ ⊕ Fin j) f j) c) := by
  ext1 x
  rcases x with (x | x) | x
  · rfl
  · rcases H : finSumFinEquiv.symm (finCongr (by omega : l = c + j) x) with a | a <;>
      simp [stdOrd, -finCongr_apply, H]
  · rfl
end GlobalTheory.SymCompare
