-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.exists_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:51.645151+00:00
-- url     : https://prove2.me/submissions/6ffe8c69-086b-410f-88f5-a6bb4240698c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
import Theorems.Thm_GlobalTheory_LogDerivHigher_main
import Theorems.Thm_GlobalTheory_LogDerivZeros_main


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
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t L : ℝ),
    Real.log (q * (|t| + 2)) ≤ L → ∃ W : Multiset ℂ,
      (∀ w : ℂ, ‖w - (2 + t * I)‖ ≤ 3 → w ≠ 1 → LFunction χ w = 0 → W.count w = ord χ w) ∧
      (W.card : ℝ) ≤ C * L ∧ ∀ k : ℕ,
        (derSeries (fun n : ℕ => χ (n : ZMod q)) k (2 + t * I)).re + (powSum W t (k + 1)).re ≤
          (if χ = 1 then 1 / ((2 : ℂ) + t * I - 1) ^ (k + 1) else 0).re + 2 * C * L / 2 ^ (k + 1) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivHigher.main
  refine ⟨C, hC, fun q _ χ t L hL => ?_⟩
  obtain ⟨hfin, hsum, -⟩ := H q χ 2 t 0 (by norm_num) le_rfl
  have hCL : C * Real.log (q * (|t| + 2)) ≤ C * L := by gcongr
  refine ⟨∑ w ∈ hfin.toFinset, Multiset.replicate (ord χ w) w, fun w h1 h2 h3 => ?_, ?_, fun k => ?_⟩
  · have hw : w ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨h1, Or.inr h2, h3⟩
    rw [Multiset.count_sum', Finset.sum_eq_single_of_mem w hw]
    · simp
    · intro b _ hb
      rw [Multiset.count_replicate, if_neg hb]
  · rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    rw [Multiset.card_sum]
    simp only [Multiset.card_replicate]
    push_cast
    linarith
  · obtain ⟨-, -, h⟩ := H q χ 2 t k (by norm_num) le_rfl
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h
    have e : powSum (∑ w ∈ hfin.toFinset, Multiset.replicate (ord χ w) w) t (k + 1) =
        ∑ w ∈ hfin.toFinset, (ord χ w : ℂ) / (((2 : ℝ) : ℂ) + t * I - w) ^ (k + 1) := by
      unfold powSum
      induction hfin.toFinset using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih]
        simp [div_eq_mul_inv]
    rw [e]
    have h' := (Complex.re_le_norm _).trans h
    rw [Complex.add_re, Complex.sub_re] at h'
    have e2 : 2 * C * L / 2 ^ (k + 1) = C * L / 2 ^ k := by rw [pow_succ]; field_simp
    have h3 : C * Real.log (q * (|t| + 2)) / 2 ^ k ≤ C * L / 2 ^ k := by gcongr
    simp only [Complex.ofReal_ofNat] at h' ⊢
    linarith
end GlobalTheory.Lin.Repulsion
