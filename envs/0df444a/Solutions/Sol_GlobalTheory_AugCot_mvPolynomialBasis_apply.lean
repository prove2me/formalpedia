-- Prove2me | solution 1 for GlobalTheory.AugCot.mvPolynomialBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:14:17.533743+00:00
-- url     : https://prove2.me/submissions/2210c07d-b16f-46dc-a8f6-377a7a9952cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d

set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R σ : Type*} [CommRing R] (x : σ → R)
open MvPolynomial
namespace GlobalTheory.AugCot
theorem _root_.solution (i : σ) :
    mvPolynomialBasis x i = d (aeval x : MvPolynomial σ R →ₐ[R] R) (X i) := by
  letI : Algebra (MvPolynomial σ R) R :=
    ((aeval x : MvPolynomial σ R →ₐ[R] R) : MvPolynomial σ R →+* R).toAlgebra
  simp only [mvPolynomialBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  exact (LinearEquiv.symm_apply_eq _).2 (kaehlerEquiv_d _ _ _).symm
end GlobalTheory.AugCot
