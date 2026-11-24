-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_apply_eq_zero_and_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:27.233804+00:00
-- url     : https://prove2.me/submissions/5e03ce24-6d1f-485a-b258-da5922936479

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set Polynomial
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
namespace GlobalTheory.AffinePoints
theorem _root_.solution {K : Type*} [Field K] [Algebra K A] (p : A →ₐ[K] K)
    {S : Set (A →ₐ[K] K)} (hS : S.Finite) (hp : p ∉ S) :
    ∃ a : A, p a = 0 ∧ ∀ q ∈ S, q a = 1 := by
  classical
  have : ∀ q ∈ S, ∃ e : A, p e = 1 ∧ q e = 0 := by
    intro q hq
    obtain ⟨b, hb⟩ : ∃ b, p b ≠ q b := by
      by_contra h
      push Not at h
      exact hp (by rwa [AlgHom.ext h])
    refine ⟨(p b - q b)⁻¹ • (b - algebraMap K A (q b)), ?_, by simp⟩
    simp [inv_mul_cancel₀ (sub_ne_zero.2 hb)]
  choose! e he using this
  refine ⟨1 - ∏ q ∈ hS.toFinset, e q, ?_, fun q hq => ?_⟩
  · rw [map_sub, map_one, map_prod, Finset.prod_eq_one fun q hq => (he q (by simpa using hq)).1,
      sub_self]
  · rw [map_sub, map_one, map_prod, Finset.prod_eq_zero (i := q) (by simpa using hq) (he q hq).2,
      sub_zero]
end GlobalTheory.AffinePoints
