-- Prove2me | solution 1 for GlobalTheory.Doubling.IsRightSmooth.isKFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:25:11.585719+00:00
-- url     : https://prove2.me/submissions/c4f6d2d8-8b70-487c-b89f-3717794e3550

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
variable {K}
variable (K)
variable {δ K χ t}
namespace GlobalTheory.Doubling
namespace IsRightSmooth
theorem _root_.solution [TopologicalSpace G] [IsTopologicalGroup G] {Φ : G → ℂ} (h : IsRightSmooth Φ)
    (hK : IsCompact (K : Set G)) : IsKFinite K Φ := by
  obtain ⟨U, hU, h⟩ := h
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun x : G => (fun y => x⁻¹ * y) ⁻¹' (U : Set G))
    (fun x => hU.preimage (continuous_const_mul x⁻¹)) fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩
  refine isKFinite_iff.2 ⟨Submodule.span ℂ ((fun x g => Φ (g * x)) '' (T : Set G)),
    FiniteDimensional.span_of_finite ℂ (T.finite_toSet.image _), fun k hk => ?_⟩
  obtain ⟨x, hx, hu⟩ := Set.mem_iUnion₂.1 (hT hk)
  refine Submodule.subset_span ⟨x, hx, funext fun g => ?_⟩
  change Φ (g * x) = Φ (g * k)
  rw [← h (g * x) _ hu, mul_assoc, mul_inv_cancel_left]
end IsRightSmooth
end GlobalTheory.Doubling
