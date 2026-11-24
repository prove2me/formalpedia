-- Prove2me | solution 1 for GlobalTheory.EigenSplit.det_sq_eq_discr_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:07:55.842855+00:00
-- url     : https://prove2.me/submissions/25c9e337-4464-4450-80e3-1c1003fe0971

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_of_field
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    {σ : ι → 𝓞 E →+* S} (hσ : Function.Injective σ) (b : Module.Basis ι ℤ (𝓞 E)) :
    (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : S) := by
  let L := FractionRing S
  have hL : Function.Injective (algebraMap S L) := IsFractionRing.injective S L
  have hinj : ∀ i, Function.Injective ((algebraMap S L).comp (σ i)) := by
    intro i
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  let φ : ι → E →+* L := fun i => IsFractionRing.lift (hinj i)
  have hφσ : ∀ i (a : 𝓞 E), φ i a = algebraMap S L (σ i a) := fun i a =>
    IsFractionRing.lift_algebraMap (hinj i) a
  have hφ : Function.Injective φ := fun i j hij => hσ (RingHom.ext fun a => hL (by
    rw [← hφσ, ← hφσ, hij]))
  have := det_sq_eq_discr_of_field hφ b
  apply hL
  rw [map_pow, RingHom.map_det, map_intCast, ← this]
  congr 2
  ext i j
  simp [hφσ]
end GlobalTheory.EigenSplit
