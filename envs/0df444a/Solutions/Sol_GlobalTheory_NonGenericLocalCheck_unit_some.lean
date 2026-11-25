-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.unit_some
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:25.817797+00:00
-- url     : https://prove2.me/submissions/33eb8624-c606-4a1b-9c06-2c4e291d5ac1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable (M) (m : ℕ)
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution (g : SplitG M.L) : ∃ v : 𝒪[F], (v : F) * -(1 + (g.q : F) * g.q) = 1 := by
  have hle : valuation F (g.q : F) ≤ 1 := g.q.2
  have hq1 : valuation F (g.q : F) < 1 := by
    refine lt_of_le_of_ne hle fun h1 => g.q_irr.not_isUnit ?_
    exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.mpr h1
  have hnu : ¬ IsUnit (g.q * g.q) := fun h => g.q_irr.not_isUnit (isUnit_of_mul_isUnit_left h)
  have hqq : valuation F ((g.q : F) * g.q) < 1 := by
    have hle2 : valuation F ((g.q * g.q : 𝒪[F]) : F) ≤ 1 := (g.q * g.q).2
    refine lt_of_le_of_ne hle2 fun h1 => hnu ?_
    exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.mpr h1
  have hv : valuation F (1 + (g.q : F) * g.q) = 1 := Valuation.map_one_add_of_lt (valuation F) hqq
  have hne : (1 + (g.q : F) * g.q) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  refine ⟨⟨-(1 + (g.q : F) * g.q)⁻¹, ?_⟩, ?_⟩
  · change valuation F _ ≤ 1
    simp only [Valuation.map_neg, map_inv₀, hv, inv_one, le_refl]
  · change -(1 + (g.q : F) * g.q)⁻¹ * -(1 + (g.q : F) * g.q) = 1
    rw [neg_mul_neg, inv_mul_cancel₀ hne]
end GlobalTheory.NonGenericLocalCheck
