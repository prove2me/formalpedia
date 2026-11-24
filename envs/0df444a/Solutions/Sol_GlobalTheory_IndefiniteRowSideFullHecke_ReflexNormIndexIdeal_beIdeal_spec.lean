-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.beIdeal_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:39:47.100003+00:00
-- url     : https://prove2.me/submissions/6c80972a-140a-45d1-a333-1c04af1c37c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ReflexNormIndexIdeal_isBe_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
variable {Dw c}
namespace GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
theorem _root_.solution (hK : ReflexLe Dw c) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : IsBe Dw c 𝔞 (beIdeal hK 𝔞 h𝔞) := by
  unfold beIdeal
  split_ifs with h
  · exact h ▸ isBe_top Dw c
  · exact (hK 𝔞 h𝔞).choose_spec
end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
