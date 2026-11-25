-- Prove2me | solution 1 for GlobalTheory.SectionBasis.tmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:45.38512+00:00
-- url     : https://prove2.me/submissions/0bccfcc9-d9ce-4373-ad7b-f0e67ca3299a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
import Theorems.Thm_GlobalTheory_SectionBasis_incl_apply

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
theorem _root_.solution (a : K') (ω : Ω) : a ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω) =
    algebraMap K' (K' ⊗[Kl] (Kl ⊗[K] Ω)) a * incl K Kl K' ω := by
  rw [incl_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  simp
end GlobalTheory.SectionBasis
