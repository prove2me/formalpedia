-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.CellSplit.pr_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:20:26.106806+00:00
-- url     : https://prove2.me/submissions/3ff2dba1-95b1-43ef-a508-c90719ca3c21

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_glPr_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM
variable {k R S E₁ E₂ : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [Algebra k E₁] [CommRing E₂]
  (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (s : S ≃+* E₁ × E₂)
  (hc1 : ∀ x, (s (c x)).1 = c₁ (s x).1) (hc2 : ∀ x, (s (c x)).2 = c₂ (s x).2)
variable {β : Type} [Fintype β] [DecidableEq β] (J : Matrix β β S)
include hc1
namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit
theorem _root_.solution (g : UG c (dbl J)) : glPr s (g : GL (β ⊕ β) S) ∈ UG c₁ (dbl (J.map (pr₁ s))) := by
  have hg : ((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S)ᵀ * dbl J *
      ((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S).map c = dbl J := g.2
  show ((glPr s (g : GL (β ⊕ β) S) : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁)ᵀ * dbl (J.map (pr₁ s)) *
      ((glPr s (g : GL (β ⊕ β) S) : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁).map c₁ = dbl (J.map (pr₁ s))
  rw [glPr_coe]
  have h1 := congrArg (fun M => M.map (pr₁ s)) hg
  simp only [Matrix.map_mul, map_c₁ c c₁ s hc1, Matrix.transpose_map, dbl_map] at h1
  exact h1
end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
