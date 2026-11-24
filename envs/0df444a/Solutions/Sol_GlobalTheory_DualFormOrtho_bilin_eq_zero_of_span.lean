-- Prove2me | solution 1 for GlobalTheory.DualFormOrtho.bilin_eq_zero_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:57.702225+00:00
-- url     : https://prove2.me/submissions/52bde412-e43c-4bf7-a72e-b6d3af95bb1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualFormValueOfValues
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DualFormOrtho
namespace GlobalTheory.DualFormOrtho
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (B : LinearMap.BilinForm ℂ V) {s t : Set V}
    (h : ∀ u ∈ s, ∀ v ∈ t, B u v = 0) {a b : V} (ha : a ∈ Submodule.span ℂ s) (hb : b ∈ Submodule.span ℂ t) : B a b = 0 := by
  induction ha using Submodule.span_induction with
  | mem u hu =>
    induction hb using Submodule.span_induction with
    | mem v hv => exact h u hu v hv
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]
end GlobalTheory.DualFormOrtho
