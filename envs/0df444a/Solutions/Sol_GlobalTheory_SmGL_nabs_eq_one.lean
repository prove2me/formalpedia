-- Prove2me | solution 1 for GlobalTheory.SmGL.nabs_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:43.400211+00:00
-- url     : https://prove2.me/submissions/f4dbb6dd-fb32-4ba3-88b4-4986518aebed

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
open scoped Pointwise
namespace GlobalTheory.SmGL
theorem _root_.solution {x : kˣ} (hx : valuation k (x : k) = 1) : nabs k x = 1 := by
  borelize k
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  let K : TopologicalSpace.PositiveCompacts k := ⟨⟨(𝒪[k] : Set k), hc⟩, by
    rw [show interior ((⟨(𝒪[k] : Set k), hc⟩ : TopologicalSpace.Compacts k).carrier) =
      (𝒪[k] : Set k) from ho.interior_eq]
    exact ⟨0, zero_mem _⟩⟩
  have h1 : MeasureTheory.Measure.addHaarMeasure K (𝒪[k] : Set k) = 1 :=
    MeasureTheory.Measure.addHaarMeasure_self
  have hs : x • (𝒪[k] : Set k) = (𝒪[k] : Set k) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show valuation k (((x⁻¹ : kˣ) : k) * y) ≤ 1 ↔ valuation k y ≤ 1
    simp [hx]
  have := MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := MeasureTheory.Measure.addHaarMeasure K) (s := (𝒪[k] : Set k)) (g := x) (r := 1)
    (by simp [h1]) (by simp [h1]) (by simp [hs])
  simp [nabs, this]
end GlobalTheory.SmGL
