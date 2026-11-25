-- Prove2me | solution 1 for GlobalTheory.AdditiveBiext.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:40:29.6179+00:00
-- url     : https://prove2.me/submissions/a8013d0b-9ef3-4596-a914-7187d2040b14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_Comp1Scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.AdditiveBiext
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.AdditiveBiext
theorem _root_.solution : ∀ (R : Type) [CommRing R] [StarRing R] (d : ℕ), ∃ B : FB R d R,
    (∀ i, B.G.F i = X ((0 : Fin 2), i) + X ((1 : Fin 2), i)) ∧ ∀ a i, B.A.act a i = C a * X ((0 : Fin 1), i) :=
  fun R _ _ d => ⟨additiveFB R d, fun _ => rfl, fun _ _ => rfl⟩
end GlobalTheory.AdditiveBiext
