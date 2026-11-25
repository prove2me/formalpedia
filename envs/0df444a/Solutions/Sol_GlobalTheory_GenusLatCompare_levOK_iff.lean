-- Prove2me | solution 1 for GlobalTheory.GenusLatCompare.levOK_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:44:51.378543+00:00
-- url     : https://prove2.me/submissions/ba8ae8cd-8ee4-4335-b542-7b708fb8ed14

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNeZeroSmulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Theorems.Thm_GlobalTheory_GenusLatCompare_ln_eq
import Theorems.Thm_GlobalTheory_GenusLatCompare_span_smul_eq

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
namespace GlobalTheory.GenusLatCompare
theorem _root_.solution (Λ : Lat E n) (N M : ℕ) : (toGen Λ).LevOK N M ↔ Λ.Admissible M N := by
  rw [GenLat.LevOK, Lat.Admissible, span_smul_eq, ln_eq]
end GlobalTheory.GenusLatCompare
