-- Prove2me | solution 1 for GlobalTheory.WpFam.wB_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:50.533913+00:00
-- url     : https://prove2.me/submissions/19730416-1c37-4a34-bfe7-69a21f002a35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups Matrix
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.WpFam
namespace GlobalTheory.WpFam
theorem _root_.solution (N : ℕ) (x : Fin 2 → ZMod N) (τ : ℍ) :
    wB N x τ = (EisensteinSeries.G2 τ + (tauPair τ).weierstrassP (tors N τ x)) / (2 * Real.pi * Complex.I) ^ 2 := by
  rw [wB, gN, wp, add_div]
end GlobalTheory.WpFam
