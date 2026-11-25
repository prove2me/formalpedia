-- Prove2me | solution 1 for GlobalTheory.PDiv.ker_cotMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:50.266894+00:00
-- url     : https://prove2.me/submissions/3579f333-22b1-4180-ac42-f7150fc6cdac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
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
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT



set_option autoImplicit false
noncomputable section
open Coalgebra Bialgebra WithConv
open GlobalTheory
open GlobalTheory.PDiv
variable {R A C D : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing D]
  [Bialgebra R A] [Bialgebra R C] [Bialgebra R D]
namespace GlobalTheory.PDiv
theorem _root_.solution [IsCocomm R C] {f : C →ₐc[R] A} (hf : Function.Surjective f) {m : ℕ}
    (hk : RingHom.ker f = torsionIdeal R C m) :
    LinearMap.ker (cotMap f) = Ideal.span {(m : R)} • (⊤ : Submodule R (Cot R C)) := by
  ext w
  rw [LinearMap.mem_ker, cotMap_eq_zero_iff hf hk, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  exact exists_congr fun v => by simp [eq_comm]
end GlobalTheory.PDiv
