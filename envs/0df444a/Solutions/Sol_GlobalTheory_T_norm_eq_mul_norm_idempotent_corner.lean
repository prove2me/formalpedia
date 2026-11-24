-- Prove2me | solution 1 for GlobalTheory.T.norm_eq_mul_norm_idempotent_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:17.848337+00:00
-- url     : https://prove2.me/submissions/b12d49fc-95f1-455c-8abe-2a769dba24e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqMulNormIdempotentCorner
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqMulNormIdempotentCornerStatement
import Theorems.Thm_GlobalTheory_norm_eq_mul_norm_idem_corner


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by
  first | exact @GlobalTheory.norm_eq_mul_norm_idem_corner | exact GlobalTheory.norm_eq_mul_norm_idem_corner | (intros; apply GlobalTheory.norm_eq_mul_norm_idem_corner <;> assumption)
end _root_.GlobalTheory.T
