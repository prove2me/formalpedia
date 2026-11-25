-- Prove2me | solution 1 for GlobalTheory.SectionBasis.incl_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:29.885896+00:00
-- url     : https://prove2.me/submissions/581997cd-07b1-41fb-8b46-4f92ea0eae74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
namespace GlobalTheory.SectionBasis
theorem _root_.solution (c : K) :
    incl K Kl K' (algebraMap K Ω c) = algebraMap K' (K' ⊗[Kl] (Kl ⊗[K] Ω)) (algebraMap K K' c) := by
  show Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeRight (algebraMap K Ω c) :
    Kl ⊗[K] Ω) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K Kl (Kl ⊗[K] Ω), AlgHom.commutes,
    IsScalarTower.algebraMap_apply Kl K' (K' ⊗[Kl] (Kl ⊗[K] Ω)), ← IsScalarTower.algebraMap_apply K Kl K']
end GlobalTheory.SectionBasis
