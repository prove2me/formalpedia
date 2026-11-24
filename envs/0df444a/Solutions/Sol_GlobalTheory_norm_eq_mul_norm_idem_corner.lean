-- Prove2me | solution 1 for GlobalTheory.norm_eq_mul_norm_idem_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:32.985412+00:00
-- url     : https://prove2.me/submissions/94f688eb-1c85-4a43-9c55-9634dafdd92b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqMulNormIdempotentCorner
import Theorems.Thm_GlobalTheory_norm_scale_idem_add_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by
  intro K A _ _ _ _ ψ e he hea a
  have hee : e * e = e := by rw [hea e, he, map_one, one_mul]
  have hid : a = (e + (1 - e) * a) * (algebraMap K A (ψ a) * e + (1 - e)) := by
    have h1 := hea a
    linear_combination (-(algebraMap K A (ψ a) - algebraMap K A (ψ a) * a + a - 1)) * hee + h1
  conv_lhs => rw [hid]
  rw [map_mul, norm_scale_idem_add_compl ψ e he hea, mul_comm]
end GlobalTheory
