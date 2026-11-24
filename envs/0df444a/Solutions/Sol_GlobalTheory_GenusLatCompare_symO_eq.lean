-- Prove2me | solution 1 for GlobalTheory.GenusLatCompare.symO_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:06:00.832582+00:00
-- url     : https://prove2.me/submissions/13a1805b-b7db-47db-9fbd-670f0aee7ea0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNeZeroSmulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan

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
open GlobalTheory GlobalTheory.GenusLatCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable [IsCMField E]
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
namespace GlobalTheory.GenusLatCompare
theorem _root_.solution (Λ : Lat E n) : symO (Dw := Dw) c (toGen Λ) = (symLat Dw c Λ).toSubring := by
  rw [symLat, Algebra.adjoin_eq_ring_closure, symO]
  rfl
end GlobalTheory.GenusLatCompare
