-- Prove2me | solution 1 for GlobalTheory.TwistVertex.mem_level_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:13:12.975704+00:00
-- url     : https://prove2.me/submissions/4a3cb1af-3d97-4a21-be13-13816df66c45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwist
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply
import Theorems.Thm_GlobalTheory_StepData_Level_mem_map
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_mem_parahoric


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.TwistVertex
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r e n : Type*} [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e] [IsEmpty e]
  [Fintype n] [DecidableEq n] {c : ℕ} {δ : kˣ →* ℂˣ} {hδ : IsTame δ}
namespace GlobalTheory.TwistVertex
theorem _root_.solution (o : r ⊕ e ≃ n ⊕ Fin c) (x : GL (n ⊕ Fin c) k) :
    x ∈ ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).J ↔ x ∈ KO k (n ⊕ Fin c) := by
  have e0 : ∀ y : GL (n ⊕ Fin c) k, ((plainFrame (k := k) o).conj.symm y).val = y.val.submatrix o o := by
    intro y
    have : (plainFrame (k := k) o).conj.symm y = (reGL o).symm y := by
      rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply]; simp [plainFrame]
    rw [this, reGL_symm_val]
  rw [Level.mem_map, mem_parahoric, mem_KO, mem_KO, ← map_inv, e0, e0]
  refine ⟨fun ⟨⟨h1, h2⟩, _⟩ => ⟨fun i j => ?_, fun i j => ?_⟩,
    fun ⟨h1, h2⟩ => ⟨⟨fun i j => h1 _ _, fun i j => h2 _ _⟩, fun i => isEmptyElim i⟩⟩
  · simpa using h1 (o.symm i) (o.symm j)
  · have := h2 (o.symm i) (o.symm j)
    rwa [submatrix_apply, o.apply_symm_apply, o.apply_symm_apply] at this
end GlobalTheory.TwistVertex
