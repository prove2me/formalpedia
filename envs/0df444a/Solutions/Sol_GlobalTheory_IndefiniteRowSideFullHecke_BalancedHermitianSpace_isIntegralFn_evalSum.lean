-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:14.719167+00:00
-- url     : https://prove2.me/submissions/abb1726b-8a45-46aa-95a9-9bb6f850e221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_BalancedHermitianSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
open NumberField NumberField.IsCMField TensorProduct
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
open NumberField NumberField.IsCMField TensorProduct
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
omit [NumberField E] [IsCMField E] [Module (𝓞 E) Y]
namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
theorem _root_.solution (S : Submodule ℝ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y))
    {k : ℕ} (x x' : Fin k → Y) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsIntegralFn S (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.evalSum S x x') := by
  intro β hβ
  choose f hf using hβ
  refine ⟨∑ i, f (x i) (x' i), ?_⟩
  show ∑ i, (β : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y) (x i) (x' i) = _
  push_cast
  exact Finset.sum_congr rfl fun i _ => hf _ _
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
end GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
