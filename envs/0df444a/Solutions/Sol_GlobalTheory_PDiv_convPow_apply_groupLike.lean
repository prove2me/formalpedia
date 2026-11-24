-- Prove2me | solution 1 for GlobalTheory.PDiv.convPow_apply_groupLike
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:28.01608+00:00
-- url     : https://prove2.me/submissions/c181d35b-65b2-42d7-bc5a-23b157e2beeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_convMul_apply_groupLike
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply



set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
open GlobalTheory GlobalTheory.PDiv
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Bialgebra R A] [Bialgebra R C] [Algebra R B] [Algebra R D]
namespace GlobalTheory.PDiv
theorem _root_.solution (x : WithConv (A →ₐ[R] B)) {u : A} (hu : IsGroupLikeElem R u)
    (n : ℕ) : (x ^ n) u = x u ^ n := by
  induction n with
  | zero => simp [hu.counit_eq_one]
  | succ n ih => rw [pow_succ, convMul_apply_groupLike _ _ hu, ih, pow_succ]
end GlobalTheory.PDiv
