-- Prove2me | solution 1 for GlobalTheory.SmGL.ord_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:19.603357+00:00
-- url     : https://prove2.me/submissions/fa4137df-04d4-459f-b0e9-af85526270ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
namespace GlobalTheory.SmGL
theorem _root_.solution {x : kˣ} : ord k x = 0 ↔ valuation k (x : k) = 1 := by
  refine ⟨fun h => ?_, ord_eq_zero⟩
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  have h1 : WithZero.log (φ (valuation k (x : k))) = 0 := neg_eq_zero.1 h
  apply φ.strictMono.injective
  rw [map_one, ← WithZero.exp_log h0, h1, WithZero.exp_zero]
end GlobalTheory.SmGL
