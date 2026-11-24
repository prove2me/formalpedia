-- Prove2me | solution 1 for GlobalTheory.Doubling.iwAbs_mul_of_triv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:53.287813+00:00
-- url     : https://prove2.me/submissions/c4a701ab-8b29-44a0-8e2e-0c3cb4720296

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)
variable {δ K}
namespace GlobalTheory.Doubling
theorem _root_.solution (h : ∀ p : P, (p : G) ∈ K → δ p = 1) (p : P) {k : G} (hk : k ∈ K) :
    iwAbs δ K (p * k) = δ p := by
  have e : ∃ p' : P, ∃ k' ∈ K, (p : G) * k = p' * k' := ⟨p, k, hk, rfl⟩
  rw [iwAbs, dif_pos e]
  obtain ⟨k', hk', e'⟩ := e.choose_spec
  have h1 := h (p⁻¹ * e.choose) (by
    have : ((p⁻¹ * e.choose : P) : G) = k * k'⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq, mul_assoc, ← e', inv_mul_cancel_left]
    rw [this]; exact mul_mem hk (inv_mem hk'))
  rw [← mul_inv_cancel_left p e.choose, map_mul, h1, mul_one]
end GlobalTheory.Doubling
