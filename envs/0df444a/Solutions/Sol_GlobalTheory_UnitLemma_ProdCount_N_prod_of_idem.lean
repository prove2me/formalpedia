-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.N_prod_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:12:43.154018+00:00
-- url     : https://prove2.me/submissions/b4d789cb-e2ca-42dd-adae-b9b66db666b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_orbSum_prod
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_split_of_stable
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_mem_X_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {K : UQ}
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution (B₁ B₂ : InvAlg K)
    (he : ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)))
    (x₁ : B₁.A) (x₂ : B₂.A) : (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ := by
  refine orbSum_prod (A₁ := B₁.A) (A₂ := B₂.A) B₁.T B₂.T (B₁.prod B₂).T (fun t => ?_) _ _ _
    (mem_X_prod B₁ B₂ x₁ x₂) (fun L hL => split_of_stable _ he L hL.2.1)
  exact Prod.ext_iff
end GlobalTheory.UnitLemma.ProdCount
