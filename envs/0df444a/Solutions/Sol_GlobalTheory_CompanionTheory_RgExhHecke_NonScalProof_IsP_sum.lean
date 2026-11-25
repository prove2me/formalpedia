-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.IsP.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:45.196063+00:00
-- url     : https://prove2.me/submissions/3b5a577b-45dd-427f-bff6-b895944aa5cd

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → ℂ → A} (hf : ∀ i, IsP (f i)) :
    IsP (fun t => ∑ i ∈ s, f i t) := by
  choose p hp using hf
  exact ⟨∑ i ∈ s, p i, fun t => by simp [eval_finset_sum, hp]⟩
end IsP
end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
