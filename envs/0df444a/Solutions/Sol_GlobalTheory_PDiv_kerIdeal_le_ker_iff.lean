-- Prove2me | solution 1 for GlobalTheory.PDiv.kerIdeal_le_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:54.063697+00:00
-- url     : https://prove2.me/submissions/2c0295f6-669f-49ef-8f42-50b8aa2c8c01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
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
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]
namespace GlobalTheory.PDiv
theorem _root_.solution (f : C →ₐc[R] A) {E : Type*} [CommRing E] [Algebra R E]
    (x : A →ₐ[R] E) :
    kerIdeal f ≤ RingHom.ker x ↔ ∀ c, x (f c) = algebraMap R E (counit c) := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · intro h c
    have := h (x := c - algebraMap R C (counit c)) (by simp [RingHom.mem_ker])
    rw [Ideal.mem_comap, RingHom.mem_ker, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes,
      sub_eq_zero] at this
    exact this
  · intro h c hc
    have hc' : counit (R := R) c = 0 := hc
    simp [RingHom.mem_ker, h, hc']
end GlobalTheory.PDiv
