-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omega_eq_om
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:20.363812+00:00
-- url     : https://prove2.me/submissions/b68eac3d-540f-4242-b7a4-d40bc7b11277

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Theorems.Thm_GlobalTheory_SmGL_val_absPow_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable (a b)
variable {a b}
namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
theorem _root_.solution (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)) :
    (omega a b μ (g, h) Φ).1 = om μ⁻¹ g h Φ.1 := by
  funext x
  have h1 : ((Fintype.card b : ℂ) / 2) = (((Fintype.card b : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  have h2 : (-(Fintype.card a : ℂ) / 2) = ((-(Fintype.card a : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  show (omChar a b μ (g, h) : ℂ) * Φ.1 (act x (g, h)) = _
  simp only [omChar, om, act, MonoidHom.mul_apply, MonoidHom.comp_apply, detChar_apply, Units.val_mul, h1, h2,
    val_absPow_ofReal, MonoidHom.inv_apply, inv_inv, MonoidHom.coe_fst, MonoidHom.coe_snd]
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
