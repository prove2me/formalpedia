-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.be_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:39.450674+00:00
-- url     : https://prove2.me/submissions/6978e941-e10a-41ce-bd50-d7d1b0973c37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ReflexNormIndexIdeal_beIdeal_spec

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
theorem _root_.solution (hK : ReflexLe Dw c) (Λ : Lat E n) : IsBeLat Dw c Λ (be hK Λ) := beIdeal_spec hK _ _
end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
