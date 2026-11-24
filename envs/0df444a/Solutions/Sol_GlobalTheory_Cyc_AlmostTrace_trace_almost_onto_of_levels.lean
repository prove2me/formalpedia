-- Prove2me | solution 1 for GlobalTheory.Cyc.AlmostTrace.trace_almost_onto_of_levels
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:04.158922+00:00
-- url     : https://prove2.me/submissions/837300c6-85db-488a-94aa-0e048fc40370

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_le_Kinf
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Hinf_le_Gj
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_sum_mem_Kinf
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_exists_finite_level

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AlmostTrace
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.AlmostTrace
theorem _root_.solution
    (hd : ∀ (K L' : FinExt l) (ε : ℝ), 0 < ε → ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ S : Finset (GQ l),
      (∀ s ∈ S, s ∈ Gj K i) →
      (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup) →
      ∃ b : Om l, b ∈ L'.1 ⊔ Ks K i ∧ ‖b‖ ≤ 1 ∧ 1 - ε ≤ ‖∑ s ∈ S, s b‖)
    (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, zero_mem _, by simp, by simp [ha0]⟩
  obtain ⟨L', hL'L, i₀, hi₀⟩ := exists_finite_level K L S hS hrep
  have hε : 0 < 1 - ‖a‖ := by linarith
  obtain ⟨i₁, hi₁⟩ := hd K L' (1 - ‖a‖) hε
  obtain ⟨b₀, hb₀, hb₀1, htr⟩ := hi₁ (max i₀ i₁) (le_max_right _ _) S
    (fun s hs => Hinf_le_Gj K _ (hS s hs)) (hi₀ (max i₀ i₁) (le_max_left _ _))
  have hb₀L : b₀ ∈ L := (sup_le hL'L ((Ks_le_Kinf K _).trans hKL)) hb₀
  have htK : ∑ s ∈ S, s b₀ ∈ Kinf K := sum_mem_Kinf K L S hS hrep hb₀L
  set t := ∑ s ∈ S, s b₀ with ht
  have hta : ‖a‖ ≤ ‖t‖ := by linarith
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hta
    exact ha0 (norm_le_zero_iff.1 hta)
  have hc : a / t ∈ Kinf K := div_mem ha htK
  refine ⟨a / t * b₀, mul_mem (hKL hc) hb₀L, ?_, ?_⟩
  · rw [norm_mul, norm_div]
    have h1 : ‖a‖ / ‖t‖ ≤ 1 := (div_le_one (norm_pos_iff.2 ht0)).2 hta
    calc ‖a‖ / ‖t‖ * ‖b₀‖ ≤ 1 * 1 := mul_le_mul h1 hb₀1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have hfix : ∀ s ∈ S, s (a / t) = a / t := fun s hs =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hS s hs) _ hc
    rw [Finset.sum_congr rfl fun s hs => by rw [map_mul, hfix s hs], ← Finset.mul_sum,
      ← ht, div_mul_cancel₀ a ht0]
end GlobalTheory.Cyc.AlmostTrace
