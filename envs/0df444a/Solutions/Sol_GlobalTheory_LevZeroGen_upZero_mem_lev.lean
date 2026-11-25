-- Prove2me | solution 1 for GlobalTheory.LevZeroGen.upZero_mem_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:07:07.482063+00:00
-- url     : https://prove2.me/submissions/c97fd9b6-dd1f-46ec-a6db-0033d8166e91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Theorems.Thm_GlobalTheory_StepData_Level_mem_map
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_iter_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.LevZeroGen
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : _root_.GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LevZeroGen
namespace _root_.GlobalTheory.LevZeroGen
theorem _root_.solution (x : GL (Fin κ ⊕ Fin (s + 1)) k) :
    _root_.GlobalTheory.LevZeroGen.upZero S t x ∈
        ((S.T t).lev 0 (s + 1)
          (Nat.zero_add _)).J ↔
      x ∈ S.P.J := by
  show _ ∈ (_root_.GlobalTheory.StepData.Level.map _ _).J ↔ _
  rw [_root_.GlobalTheory.StepData.Level.mem_map, _root_.GlobalTheory.LevZeroGen.upZero,
    MulEquiv.trans_apply]
  erw [MulEquiv.symm_apply_apply]
  rw [_root_.GlobalTheory.StepData.TypeDatum.iter_zero]
  unfold _root_.GlobalTheory.StepData.TypeDatum.reindex
  show _ ∈ (_root_.GlobalTheory.StepData.Level.map _ _).J ↔ _
  rw [_root_.GlobalTheory.StepData.Level.mem_map, MulEquiv.symm_apply_apply]
end _root_.GlobalTheory.LevZeroGen
end GlobalTheory.LevZeroGen
