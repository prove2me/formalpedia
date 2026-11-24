-- Prove2me | solution 1 for GlobalTheory.SymChain.IterPattern.iter_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:08:42.291602+00:00
-- url     : https://prove2.me/submissions/9e01a262-a8b8-4c27-8b78-8843ac7ae01c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPatternStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_base_iff
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_step_iff
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
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.IterPattern
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ρ κ l j : ℕ} {t : Type}
variable [Fintype t] [DecidableEq t]
namespace GlobalTheory.SymChain.IterPattern
theorem _root_.solution (P : TypeDatum k (Fin κ ⊕ Fin l)) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (j : ℕ) (g : GL (Ix (Fin κ ⊕ Fin l) t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero]
    exact base_iff P hP g
  | succ j ih =>
    rw [TypeDatum.iter_succ]
    exact step_iff _ (μ (j + 1)) (hμ _) ih g
end GlobalTheory.SymChain.IterPattern
