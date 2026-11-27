-- Prove2me | solution 1 for GlobalTheory.T.rho_prod_finiteAlgebraWithInvolution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:25.020254+00:00
-- url     : https://prove2.me/submissions/f68cf7bc-95d6-44e2-8ac9-e5524640f135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoProdFiniteAlgebraWithInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoProdFiniteAlgebraWithInvolutionStatement
import Theorems.Thm_GlobalTheory_RhoProd_rho_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (w₁ : B₁.A) (w₂ : B₂.A), (B₁.prod B₂).rho ((w₁, w₂) : B₁.A × B₂.A) = B₁.rho w₁ * B₂.rho w₂ := by
  first | exact @GlobalTheory.RhoProd.rho_prod | exact GlobalTheory.RhoProd.rho_prod | (intros; apply GlobalTheory.RhoProd.rho_prod <;> assumption)
end _root_.GlobalTheory.T
