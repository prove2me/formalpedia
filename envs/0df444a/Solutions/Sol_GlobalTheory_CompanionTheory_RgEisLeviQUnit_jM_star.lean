-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:34.746665+00:00
-- url     : https://prove2.me/submissions/e29d8aa8-b404-4a6e-abda-b397c0a50c02

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {α κ β : Type} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (e : κ → α) (m : Matrix κ κ ℂ) : star (jM e m) = jM e (star m) := by
  have hs : ∀ {n : Type} [Fintype n] (x : Matrix n n ℂ), star x = (x.map (starRingEnd ℂ))ᵀ := fun x => by
    ext a b
    rfl
  rw [hs, hs, jM_map, jM_transpose]
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
