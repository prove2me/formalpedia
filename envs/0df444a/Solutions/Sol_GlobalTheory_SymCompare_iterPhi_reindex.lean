-- Prove2me | solution 1 for GlobalTheory.SymCompare.iterPhi_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:50:01.001907+00:00
-- url     : https://prove2.me/submissions/e79db5cd-d08c-4930-8795-6b133b8c39da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_SymCompare_Phi_reindex
import Theorems.Thm_GlobalTheory_SymCompare_iter_reindex

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
theorem _root_.solution (f : t ≃ t') (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    (x : Matrix (Ix r t' (j + 1)) (Ix r t' j) k) :
    P.iterPhi t' μ hμ j x = P.iterPhi t μ hμ j (x.submatrix (eI r f (j + 1)) (eI r f j)) := by
  unfold TypeDatum.iterPhi
  rw [iter_reindex f, Phi_reindex _ _ f]
  congr 1
  ext ((i | i) | i) l <;> rfl
end GlobalTheory.SymCompare
