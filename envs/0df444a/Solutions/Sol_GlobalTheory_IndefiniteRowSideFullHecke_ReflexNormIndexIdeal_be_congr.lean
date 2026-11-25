-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.be_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:08.096721+00:00
-- url     : https://prove2.me/submissions/32854508-27e6-483c-8859-2c1627bd96fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal

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
theorem _root_.solution (hK : ReflexLe Dw c) {n' : ℕ} {Λ : Lat E n} {Λ' : Lat E n'} (h : latIdeal Λ = latIdeal Λ') :
    be hK Λ = be hK Λ' := by
  simp only [be, h]
end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
