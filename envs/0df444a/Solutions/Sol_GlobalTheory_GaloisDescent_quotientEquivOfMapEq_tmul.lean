-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.quotientEquivOfMapEq_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:47.965375+00:00
-- url     : https://prove2.me/submissions/f1197586-f2ff-4724-9a27-6fe040adf98d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
open Algebra.TensorProduct
variable {K L A G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {A : Type*} [CommRing A] [Algebra K A] (I₀ : Ideal A)
    (I : Ideal (L ⊗[K] A)) (h : I₀.map (includeRight : A →ₐ[K] L ⊗[K] A) = I) (l : L) (a : A) :
    quotientEquivOfMapEq I₀ I h (l ⊗ₜ Ideal.Quotient.mk I₀ a) = Ideal.Quotient.mk I (l ⊗ₜ a) :=
  rfl
end GlobalTheory.GaloisDescent
