-- Prove2me | solution 1 for GlobalTheory.SymCompare.Phi_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:33:01.366387+00:00
-- url     : https://prove2.me/submissions/d239025e-4112-42dd-9d14-ef51fb6ce44b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_SymCompare_exists_reindex_iff
import Theorems.Thm_GlobalTheory_SymCompare_maxM_submatrix
import Theorems.Thm_GlobalTheory_SymCompare_det_reGL_symm

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
omit [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m']
namespace GlobalTheory.SymCompare
theorem _root_.solution (P : TypeDatum k n) (e : n ≃ m) (f : n' ≃ m') (μ : kˣ →* ℂˣ) (x : Matrix (m ⊕ m') m k) :
    (P.reindex e).Phi m' μ x = P.Phi n' μ (x.submatrix (e.sumCongr f) e) := by
  have hi : (P.reindex e).Phi m' μ x ≠ 0 ↔ P.Phi n' μ (x.submatrix (e.sumCongr f) e) ≠ 0 := by
    rw [TypeDatum.Phi_ne_zero_iff, TypeDatum.Phi_ne_zero_iff, exists_reindex_iff, ← maxM_submatrix f e]
    rfl
  by_cases h : (P.reindex e).Phi m' μ x = 0
  · rw [h, not_not.1 (hi.not.1 (not_not.2 h))]
  · obtain ⟨⟨g, hg, eg⟩, h2⟩ := (TypeDatum.Phi_ne_zero_iff _ _).1 h
    rw [TypeDatum.Phi_of_mem _ μ ⟨g, hg⟩ eg h2, TypeDatum.Phi_of_mem _ μ (x := x.submatrix (e.sumCongr f) e) ⟨(reGL e).symm g, hg⟩
      (by rw [reGL_symm_val, eg]; rfl) ((maxM_submatrix f e _).2 h2), det_reGL_symm]
    rfl
end GlobalTheory.SymCompare
