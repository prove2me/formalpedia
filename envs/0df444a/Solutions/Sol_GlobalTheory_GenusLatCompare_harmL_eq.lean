-- Prove2me | solution 1 for GlobalTheory.GenusLatCompare.harmL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:44:45.628942+00:00
-- url     : https://prove2.me/submissions/6df042ec-115a-4975-9445-ee4a6d6f4ce7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNeZeroSmulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Theorems.Thm_GlobalTheory_GenusLatCompare_symO_eq

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
theorem _root_.solution (Λ : Lat E n) (a : (E →+* ℂ) × ℕ → ℕ) :
    harmL (Dw := Dw) c (toGen Λ) a = harmLat Dw c a Λ := by
  ext P
  simp only [harmL, harmLat, symO_eq, Set.mem_setOf_eq]
  rfl
end GlobalTheory.GenusLatCompare
