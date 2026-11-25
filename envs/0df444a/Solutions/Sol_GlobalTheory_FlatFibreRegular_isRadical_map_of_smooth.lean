-- Prove2me | solution 1 for GlobalTheory.FlatFibreRegular.isRadical_map_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:33:25.756026+00:00
-- url     : https://prove2.me/submissions/820c0ab7-6b45-4a58-a6fa-3f80c1e1a24f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
import Theorems.Thm_GlobalTheory_isReduced_algebra_of_smooth_of_isReduced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular
namespace GlobalTheory.FlatFibreRegular
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (𝔭 : Ideal A) [𝔭.IsPrime] : (𝔭.map (algebraMap A B)).IsRadical := by
  haveI : _root_.IsReduced ((A ⧸ 𝔭) ⊗[A] B) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (A ⧸ 𝔭) _
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B 𝔭).toRingEquiv.trans
    (Algebra.TensorProduct.comm A B (A ⧸ 𝔭)).toRingEquiv
  haveI : _root_.IsReduced (B ⧸ 𝔭.map (algebraMap A B)) :=
    isReduced_of_injective e.toRingHom e.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).2 this
end GlobalTheory.FlatFibreRegular
