-- Prove2me | solution 1 for GlobalTheory.LevZeroUp.lam_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:16:50.170655+00:00
-- url     : https://prove2.me/submissions/3be3b004-a761-4a1f-ac30-b6e3c6c21fb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL
import Theorems.Thm_GlobalTheory_LevZeroUp_simpleSum_upZero
import Theorems.Thm_GlobalTheory_LevZeroUp_superSum_one
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.LevZeroUp
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LevZeroGen GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LevZeroUp
theorem _root_.solution (n : S.P.J) (hn : n.1 ∈ N k (Fin κ) (s + 1) (S.ρ + 1)) :
    ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (simpleSum (upZero S t n.1)) : ℂ) := by
  rw [S.sym.2 n, simpleSum_upZero]
  have h11 : (n : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ = 1 := by
    rw [Model.mem_N_iff] at hn
    ext i j
    simpa [toBlocks₁₁, Matrix.one_apply] using hn (.inl i) (.inl j) (by simp [lev])
  rw [h11, superSum_one]
  simp
end GlobalTheory.LevZeroUp
