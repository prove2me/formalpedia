-- Prove2me | solution 1 for GlobalTheory.SymCompare.typeChain_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:29.928403+00:00
-- url     : https://prove2.me/submissions/08d19d3c-b93b-44ae-9800-b5d40a22ce01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_SymCompare_reGL_embA
import Theorems.Thm_GlobalTheory_SymCompare_coords_submatrix
import Theorems.Thm_GlobalTheory_SymCompare_iterPhi_reindex
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
    (hμ : ∀ j, IsTame (μ j)) (j c : ℕ) (h : j + c = s) :
    (typeChain t' ϖ P μ hμ).Phi j c h = fun x => (typeChain t ϖ P μ hμ).Phi j c h
      (x.submatrix (sE (eI (κ ⊕ Fin (j + 1)) f (j + 1)) c) (sE (eI (κ ⊕ Fin j) f j) (c + 1))) := by
  funext x
  change P.iterPhi t' μ hμ j _ = P.iterPhi t μ hμ j _
  rw [iterPhi_reindex f]
  exact congrArg _ (coords_submatrix (typeFrame ϖ (stdOrd κ t (j + 1) c (by omega)))
    (typeFrame ϖ (stdOrd κ t' (j + 1) c (by omega))) _ _ (stdOrd_eI κ f (j + 1) c (by omega)) (reGL_embA _ _).symm
    (typeFrame ϖ (stdOrd κ t j (c + 1) (by omega))) (typeFrame ϖ (stdOrd κ t' j (c + 1) (by omega))) _ _
    (stdOrd_eI κ f j (c + 1) (by omega)) (reGL_embA _ _).symm x)
end GlobalTheory.SymCompare
