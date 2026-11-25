-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.IsP.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:55:24.149877+00:00
-- url     : https://prove2.me/submissions/f5964460-7f9a-45e4-9f84-70688d1cb708

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
namespace IsP
theorem _root_.solution {f g : ℂ → A} (hf : IsP f) (hg : IsP g) : IsP (fun t => f t * g t) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p * q, fun t => ?_⟩
  show f t * g t = _
  rw [hp, hq]
  exact (eval₂_mul_noncomm (RingHom.id A) (algebraMap ℂ A t)
    (fun k => (Algebra.commutes t _).symm)).symm
end IsP
end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
