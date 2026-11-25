-- Prove2me | solution 1 for GlobalTheory.HTLat.isSplitting_embO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:48:20.733515+00:00
-- url     : https://prove2.me/submissions/6efc7a7b-c431-4636-acf2-9c5fa3da164e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_HTLat_algebraMap_embO
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_of_isDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.HTLat
namespace _root_.GlobalTheory.HTLat
theorem _root_.solution [IsAlgClosed C] [CharZero C] :
    _root_.GlobalTheory.EigenSplit.IsSplitting
      (fun φ : E →+* C => (algebraMap O C).comp (_root_.GlobalTheory.HTLat.embO hv φ)) := by
  classical
  have hfun : (fun φ : E →+* C => (algebraMap O C).comp (_root_.GlobalTheory.HTLat.embO hv φ)) =
      fun φ => (RingHom.id C).comp (φ.comp (algebraMap (𝓞 E) E)) := by
    funext φ
    ext a
    simp [_root_.GlobalTheory.HTLat.algebraMap_embO]
  rw [hfun]
  refine _root_.GlobalTheory.EigenSplit.isSplitting_of_isDomain (E := E) ?_
    (NumberField.Embeddings.card E C) _ ?_
  · intro φ ψ h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  · exact isUnit_iff_ne_zero.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
end _root_.GlobalTheory.HTLat
end GlobalTheory.HTLat
