-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SwapInt.isIntegral_map_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:16.452021+00:00
-- url     : https://prove2.me/submissions/7729f6f9-dc76-4bfa-8f21-e3a93db9acd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SwapInt
namespace GlobalTheory.UnitLemma.SwapInt
theorem _root_.solution {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] [Algebra O S]
    [Algebra O S'] (κ : O →+* O) (ψ : S →+* S')
    (hψ : ∀ o, ψ (algebraMap O S o) = algebraMap O S' (κ o)) {y : S} (h : IsIntegral O y) :
    IsIntegral O (ψ y) := by
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map κ, hm.map κ, ?_⟩
  rw [eval₂_map]
  have e : (algebraMap O S').comp κ = ψ.comp (algebraMap O S) := by
    ext o; simp [hψ]
  rw [e, ← hom_eval₂, hp, map_zero]
end GlobalTheory.UnitLemma.SwapInt
