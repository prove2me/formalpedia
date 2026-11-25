-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.be_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:11.306587+00:00
-- url     : https://prove2.me/submissions/68ffc456-62b5-410c-a27b-fa40e98b5e35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ReflexNormIndexIdeal_latIdeal_std

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
theorem _root_.solution (hK : ReflexLe Dw c) : be hK (Lat.std E n) = 1 := by
  simp [be, beIdeal, latIdeal_std]
end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
