-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.isUnit_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:15.307024+00:00
-- url     : https://prove2.me/submissions/5031c97c-64c7-4f4d-b52b-3abf0252597d

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck
namespace GlobalTheory.CyclicNormCheck
theorem _root_.solution {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] {x : F} (hx : x ≠ 0) {y : K ⊗[F] E}
    (h : Algebra.norm K y = algebraMap F K x) : IsUnit y := by
  have h0 : LinearMap.det (LinearMap.mul K (K ⊗[F] E) y) ≠ 0 := by
    have : Algebra.norm K y ≠ 0 := by rw [h]; exact (map_ne_zero _).2 hx
    simpa [Algebra.norm_apply] using this
  have hu : IsUnit (LinearMap.mul K (K ⊗[F] E) y) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h0)
  have hs := ((Module.End.isUnit_iff _).1 hu).2
  obtain ⟨z, hz⟩ := hs 1
  exact IsUnit.of_mul_eq_one z (by simpa using hz)
end GlobalTheory.CyclicNormCheck
