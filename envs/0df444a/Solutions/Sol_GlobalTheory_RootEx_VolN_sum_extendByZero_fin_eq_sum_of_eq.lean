-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.sum_extendByZero_fin_eq_sum_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:31.938118+00:00
-- url     : https://prove2.me/submissions/7ce4c20e-33d0-476e-82a4-13fd3c895d0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}]
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (w : ι × ι → k) :
    ∑ b : {rs : ι × ι // P rs.1 rs.2}, w b.1 * e b = ∑ r, ∑ s, w (r, s) * ext0 P e r s := by
  rw [← Fintype.sum_prod_type' (fun r s => w (r, s) * ext0 P e r s),
    ← Finset.sum_filter_of_ne (p := fun rs : ι × ι => P rs.1 rs.2),
    Finset.sum_subtype (p := fun rs : ι × ι => P rs.1 rs.2) (F := F) _ (by simp)]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [ext0, b.2]
  · intro x _ hx
    by_contra h
    simp [ext0, h] at hx
end GlobalTheory.RootEx.VolN
