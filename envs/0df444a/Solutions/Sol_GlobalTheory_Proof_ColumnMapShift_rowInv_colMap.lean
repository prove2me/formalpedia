-- Prove2me | solution 1 for GlobalTheory.Proof.ColumnMapShift.rowInv_colMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:13:01.367521+00:00
-- url     : https://prove2.me/submissions/7e7b1fbc-6778-4b20-9a2d-6d531807a207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColumnMapShift
import Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_rowShift_colMap

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
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.ColumnMapShift
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.Proof.ColumnMapShift
theorem _root_.solution (g : T → Fin n → Fin n → k) {P : MvPolynomial (Letter T r n) k}
    (hP : RowInv r n k P) : RowInv r n k (colMap r g P) := by
  intro σ i i' hi t
  rw [rowShift_colMap, hP σ i i' hi t]
end GlobalTheory.Proof.ColumnMapShift
