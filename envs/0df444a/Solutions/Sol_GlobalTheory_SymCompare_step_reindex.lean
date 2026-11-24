-- Prove2me | solution 1 for GlobalTheory.SymCompare.step_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:36.641573+00:00
-- url     : https://prove2.me/submissions/73c7be6c-1aad-4dd2-883d-20950207061d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_SymCompare_td_ext
import Theorems.Thm_GlobalTheory_SymCompare_reGL_symm_mem_KO
import Theorems.Thm_GlobalTheory_SymCompare_exists_reindex_iff
import Theorems.Thm_GlobalTheory_SymCompare_maxM_submatrix
import Theorems.Thm_GlobalTheory_SymCompare_det_reGL_symm
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_lam


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
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution (P : TypeDatum k n) (e : n ≃ m) (f : n' ≃ m') (μ : kˣ →* ℂˣ) (hμ : IsTame μ) :
    (P.reindex e).step m' μ hμ = (P.step n' μ hμ).reindex (e.sumCongr f) := by
  refine td_ext (fun g => ?_) fun g h h' => ?_
  · change g ∈ (P.reindex e).stepJ m' ↔ (reGL (e.sumCongr f)).symm g ∈ P.stepJ n'
    rw [TypeDatum.mem_stepJ_iff, TypeDatum.mem_stepJ_iff, reGL_symm_mem_KO, exists_reindex_iff,
      ← maxM_submatrix f e]
    rfl
  · have h1 := (P.reindex e).step_lam μ hμ ⟨g, h⟩ _ (TypeDatum.corner_val _ _)
    have h2 := P.step_lam μ hμ ⟨_, h'⟩ ⟨(reGL e).symm ((P.reindex e).corner ⟨g, h⟩), ((P.reindex e).corner ⟨g, h⟩).2⟩
      (by rw [reGL_symm_val, TypeDatum.corner_val]; rfl)
    have h3 := det_reGL_symm (e.sumCongr f) g
    simp only [det_reGL_symm] at h2
    refine h1.trans (Eq.trans ?_ h2.symm)
    exact congrArg₂ (· * ·) rfl (congrArg μ h3.symm)
end GlobalTheory.SymCompare
