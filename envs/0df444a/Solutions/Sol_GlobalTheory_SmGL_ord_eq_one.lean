-- Prove2me | solution 1 for GlobalTheory.SmGL.ord_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:43.010415+00:00
-- url     : https://prove2.me/submissions/4fe3cb6f-0e48-4e6b-9684-f36d8f233b2d

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
theorem _root_.solution {x : kˣ} (hx : valuation k (x : k) = uniformizer k) : ord k x = 1 := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (uniformizer k) ≠ 0 := by simp
  have key : φ (uniformizer k) = WithZero.exp (-1) := by
    apply le_antisymm
    · have : φ (uniformizer k) < φ 1 := φ.strictMono uniformizer_lt_one
      rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
    · have : φ.symm (WithZero.exp (-1)) ≤ uniformizer k := by
        rw [le_uniformizer_iff, ← map_one φ.symm]
        exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
      simpa using φ.strictMono.monotone this
  simp [ord, hx, φ, key]
end GlobalTheory.SmGL
