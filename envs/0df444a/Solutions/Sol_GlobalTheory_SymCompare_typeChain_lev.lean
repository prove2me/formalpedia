-- Prove2me | solution 1 for GlobalTheory.SymCompare.typeChain_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:33.044587+00:00
-- url     : https://prove2.me/submissions/ef5bb1be-0260-4483-835e-2821791716b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_SymCompare_reGL_embA
import Theorems.Thm_GlobalTheory_SymCompare_reGL_conj
import Theorems.Thm_GlobalTheory_SymCompare_iter_reindex
import Theorems.Thm_GlobalTheory_SymCompare_stdOrd_eI

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {s : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution (f : t ≃ t') (ϖ : kˣ) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j c : ℕ) (h : j + c = s + 1) (g : GL (XIx κ t j ⊕ Fin c) k) :
    reGL (sE (eI (κ ⊕ Fin j) f j) c) g ∈ ((typeChain t' ϖ P μ hμ).lev j c h).J ↔
      g ∈ ((typeChain t ϖ P μ hμ).lev j c h).J := by
  obtain ⟨g, rfl⟩ := (typeFrame ϖ (stdOrd κ t j c h)).conj.surjective g
  rw [← reGL_conj (typeFrame ϖ (stdOrd κ t j c h)) (typeFrame ϖ (stdOrd κ t' j c h)) _ _ (stdOrd_eI κ f j c h)
    (reGL_embA _ _).symm]
  change (typeFrame ϖ (stdOrd κ t' j c h)).conj.symm _ ∈ (P.iter t' μ hμ j).J ↔
    (typeFrame ϖ (stdOrd κ t j c h)).conj.symm _ ∈ (P.iter t μ hμ j).J
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, iter_reindex f]
  change (reGL (eI _ f j)).symm (reGL (eI _ f j) g) ∈ (P.iter t μ hμ j).J ↔ _
  rw [MulEquiv.symm_apply_apply]
end GlobalTheory.SymCompare
