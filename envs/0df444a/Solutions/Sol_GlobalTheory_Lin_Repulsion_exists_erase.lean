-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.exists_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:22:55.817053+00:00
-- url     : https://prove2.me/submissions/43993f38-9089-49e0-8fd7-0ad6ea0ed0ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
import Theorems.Thm_GlobalTheory_Lin_Repulsion_pole_pair
import Theorems.Thm_GlobalTheory_Lin_Repulsion_pole_far

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion
namespace GlobalTheory.Lin.Repulsion
theorem _root_.solution {β : ℝ} (hβ : β < 1) (hβ' : 1 / 2 ≤ β) (W : Multiset ℂ) (t : ℝ)
    (h : ‖(β : ℂ) - (2 + t * I)‖ ≤ 3 → (β : ℂ) ∈ W) : ∃ W' : Multiset ℂ, W'.card ≤ W.card ∧
      (∀ w ∈ W, w ≠ β ∨ 2 ≤ W.count w → w ∈ W') ∧ ∀ j : ℕ,
        (powSum W' t j).re + (1 / ((2 : ℂ) + t * I - 1) ^ j).re ≤
          (powSum W t j).re + j * (1 - β) + 1 / 2 ^ j := by
  by_cases hd : ‖(β : ℂ) - (2 + t * I)‖ ≤ 3
  · have hm := h hd
    refine ⟨W.erase β, Multiset.card_erase_le, fun w hw hc => ?_, fun j => ?_⟩
    · by_cases hwβ : w = β
      · subst hwβ
        have h2 := hc.resolve_left (by simp)
        rw [← Multiset.one_le_count_iff_mem, Multiset.count_erase_self]; omega
      · exact (Multiset.mem_erase_of_ne hwβ).2 hw
    · have e : powSum W t j = (1 / ((2 : ℂ) + t * I - β)) ^ j + powSum (W.erase β) t j := by
        conv_lhs => rw [← Multiset.cons_erase hm]
        unfold powSum
        rw [Multiset.map_cons, Multiset.sum_cons]
      have h1 := (Complex.re_le_norm _).trans (pole_pair (t := t) hβ j)
      rw [Complex.sub_re] at h1
      rw [e, Complex.add_re]
      have : (0 : ℝ) ≤ 1 / 2 ^ j := by positivity
      linarith
  · refine ⟨W, le_rfl, fun w hw _ => hw, fun j => ?_⟩
    have h1 := (Complex.re_le_norm _).trans (pole_far hβ hβ' hd j)
    have : (0 : ℝ) ≤ j * (1 - β) := by have : 0 ≤ 1 - β := by linarith
                                       positivity
    linarith
end GlobalTheory.Lin.Repulsion
