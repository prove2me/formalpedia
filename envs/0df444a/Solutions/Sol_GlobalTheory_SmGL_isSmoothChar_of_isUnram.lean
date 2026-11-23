-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmoothChar_of_isUnram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:42.844548+00:00
-- url     : https://prove2.me/submissions/d30b41b1-56ef-46fe-9387-a0f68379ce6d

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
theorem _root_.solution {χ : kˣ →* ℂˣ} (h : IsUnram χ) : IsSmoothChar χ := by
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have h1 : IsOpen ({x : kˣ | (x : k) ∈ (𝒪[k] : Set k)} ∩
      {x : kˣ | ((x⁻¹ : kˣ) : k) ∈ (𝒪[k] : Set k)}) :=
    (ho.preimage Units.continuous_val).inter (ho.preimage Units.continuous_coe_inv)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (h1.mem_nhds ?_) ?_)
  · exact ⟨one_mem 𝒪[k], by simpa using one_mem 𝒪[k]⟩
  · rintro x ⟨hx, hx'⟩
    have a1 : valuation k (x : k) ≤ 1 := hx
    have a2 : valuation k ((x⁻¹ : kˣ) : k) ≤ 1 := hx'
    refine h x (le_antisymm a1 ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀] at a2
    exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 a2
end GlobalTheory.SmGL
