-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.exists_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:31:16.646843+00:00
-- url     : https://prove2.me/submissions/9dcde654-8147-483e-bce9-8dc2187198b0

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {x : L} (hx : x ∈ intL L) :
    ∃ y ∈ intL L, y + σ y + x * σ x = 0 := by
  obtain ⟨hσ, hv, -, -, ⟨a, ha, ha1⟩, -⟩ := hU
  have h0 : σ a - a ≠ 0 := by
    intro h; rw [h, map_zero] at ha1; exact zero_ne_one ha1
  have h0' : a - σ a ≠ 0 := fun h => h0 (by linear_combination -h)
  refine ⟨-(σ a / (σ a - a)) * (x * σ x), ?_, ?_⟩
  · show Valued.v (-(σ a / (σ a - a)) * (x * σ x)) ≤ 1
    have hx' : Valued.v x ≤ 1 := hx
    have ha' : Valued.v a ≤ 1 := ha
    rw [map_mul, Valuation.map_neg, map_div₀, ha1, div_one, map_mul, hv, hv]
    exact mul_le_one' ha' (mul_le_one' hx' hx')
  · simp only [map_mul, map_neg, map_div₀, map_sub, hσ]
    field_simp
    ring
end GlobalTheory.SatakeWeyl.Heis
