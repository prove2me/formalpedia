-- Prove2me | solution 1 for GlobalTheory.SymCompare.iter_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:39:53.534805+00:00
-- url     : https://prove2.me/submissions/574511eb-4e88-4f20-936e-89f2ab300445

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_SymCompare_reindex_trans
import Theorems.Thm_GlobalTheory_SymCompare_step_reindex
import Theorems.Thm_GlobalTheory_SymCompare_ixSucc_eI
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_iter_succ
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_iter_zero


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
theorem _root_.solution (f : t ≃ t') (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    P.iter t' μ hμ j = (P.iter t μ hμ j).reindex (eI r f j) := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero, TypeDatum.iter_zero, reindex_trans]
    rfl
  | succ j ih =>
    rw [TypeDatum.iter_succ, TypeDatum.iter_succ, ih, step_reindex _ _ f, reindex_trans, reindex_trans, ixSucc_eI]
end GlobalTheory.SymCompare
