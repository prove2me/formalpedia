-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothPart.radical_eq_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:53.599179+00:00
-- url     : https://prove2.me/submissions/51a3d8bf-2ebc-4ca5-91be-573d37ffc964

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothPart
namespace GlobalTheory.CompanionTheory.SmoothPart
theorem _root_.solution {X : Scheme.{0}} (Z : X.IdealSheafData) [IsReduced Z.subscheme] :
    Z.radical = Z := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical Z)
  rw [Scheme.IdealSheafData.le_def]
  intro U x hx
  rw [Scheme.IdealSheafData.radical_ideal] at hx
  obtain ⟨n, hn⟩ := hx
  rw [← Z.ker_subschemeι_app U, RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsNilpotent.eq_zero ⟨n, hn⟩
end GlobalTheory.CompanionTheory.SmoothPart
