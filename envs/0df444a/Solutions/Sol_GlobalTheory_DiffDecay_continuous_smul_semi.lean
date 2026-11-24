-- Prove2me | solution 1 for GlobalTheory.DiffDecay.continuous_smul_semi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:44.610415+00:00
-- url     : https://prove2.me/submissions/bafd26d1-60a7-45a4-800d-c0b176f7249b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.DiffDecay
variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]
namespace GlobalTheory.DiffDecay
theorem _root_.solution (c : ℝ) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ f, q' f = |c| * q f :=
  ⟨(‖c‖₊ : NNReal) • q, (continuous_const.mul hq : Continuous fun f => |c| * q f), fun _ => rfl⟩
end GlobalTheory.DiffDecay
