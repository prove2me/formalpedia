-- Prove2me | solution 1 for GlobalTheory.SplitWeil.om_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:10.723277+00:00
-- url     : https://prove2.me/submissions/816662d7-9f31-4202-9626-2ed68f633b5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
namespace GlobalTheory.SplitWeil
theorem _root_.solution (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    om μ g h Φ ∈ SB (Matrix b a k) := by
  have h1 : Φ ∘ sideMul g h ∈ SB (Matrix b a k) :=
    ⟨hΦ.1.comp_continuous (sideMul g h).continuous, hΦ.2.comp_homeomorph _⟩
  exact (SB _).smul_mem _ h1
end GlobalTheory.SplitWeil
