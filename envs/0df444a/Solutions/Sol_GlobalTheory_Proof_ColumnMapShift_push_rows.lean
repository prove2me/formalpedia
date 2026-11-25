-- Prove2me | solution 1 for GlobalTheory.Proof.ColumnMapShift.push_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:09:48.16373+00:00
-- url     : https://prove2.me/submissions/13707dea-9917-4845-9f02-351e8fc1b853

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColumnMapShift
import Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_rowInv_colMap
import Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_rowDeg_colMap

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
namespace GlobalTheory.Proof.ColumnMapShift
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F), ∀ (a : (E →+* ℂ) → ℕ → ℕ), (RowInv Dw.mult n c.F P → RowInv Dw.mult n c.F (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P)) ∧ (RowDeg Dw.mult n c.F a P → RowDeg Dw.mult n c.F a (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P)) := by
  intro E _ _ _ H Dw l c n γ P a
  have e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ = colMap Dw.mult fun σ b j => embF c σ (γ b j) := rfl
  rw [e]
  exact ⟨rowInv_colMap _, rowDeg_colMap _⟩
end GlobalTheory.Proof.ColumnMapShift
