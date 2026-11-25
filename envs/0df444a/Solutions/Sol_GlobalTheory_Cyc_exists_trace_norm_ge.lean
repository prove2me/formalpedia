-- Prove2me | solution 1 for GlobalTheory.Cyc.exists_trace_norm_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:25.637234+00:00
-- url     : https://prove2.me/submissions/cc2856bf-1866-4c7e-9d3b-07646f5cfb19

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_gal
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_power_sum
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_finite_orbit
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_moved
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_finite_Ks
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_primitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open DiffSmall
namespace GlobalTheory.Cyc
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (K L' : FinExt l) (ε : ℝ), 0 < ε → ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ S : Finset (GQ l), (∀ s ∈ S, s ∈ Gj K i) → (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup) → ∃ b : Om l, b ∈ L'.1 ⊔ Ks K i ∧ ‖b‖ ≤ 1 ∧ 1 - ε ≤ ‖∑ s ∈ S, s b‖ := by
  classical
  intro l _ K L' ε hε
  obtain ⟨y, hyL, hy, hyg⟩ := exists_primitive L'
  set n := (finite_orbit y).toFinset.card with hn
  set a : ℝ := min 1 (ε / (n + 1)) with ha
  have ha0 : 0 < a := lt_min one_pos (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have hδ : 1 - ε ≤ (1 - a) ^ n := by
    have h1 := one_add_mul_le_pow (a := -a) (by linarith) n
    have h2 : a * (n + 1) ≤ ε := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    rw [sub_eq_add_neg 1 a]
    nlinarith
  obtain ⟨i₀, hi₀⟩ := exists_moved K hy n (δ := 1 - a) (by linarith) (by linarith)
  refine ⟨i₀, fun i hi S hS hu => ?_⟩
  haveI := L'.2
  haveI := finite_Ks K i
  have hsep : ∀ s ∈ S, ∀ t ∈ S, (s⁻¹ * t) y = y → s = t := by
    intro s hs t ht h
    refine (hu t (hS t ht)).unique ⟨hs, ?_⟩ ⟨ht, by simp⟩
    rw [IntermediateField.fixingSubgroup_sup]
    have h2 : s⁻¹ * t ∈ Gj K i := mul_mem (inv_mem (hS s hs)) (hS t ht)
    exact ⟨hyg _ h, h2⟩
  have hcard : S.card ≤ n := by
    refine Finset.card_le_card_of_injOn (fun s => s y) (fun s _ => ?_) fun s hs t ht h => ?_
    · simp
    · refine hsep s hs t ht ?_
      have h' : s y = t y := h
      rw [AlgEquiv.mul_apply, ← h']
      simp
  obtain ⟨x, hxE, hx, hmove⟩ := hi₀ i hi (L'.1 ⊔ Ks K i) le_sup_right
    ((le_sup_left : L'.1 ≤ _) hyL) S hcard hS hu
  obtain ⟨s₀, ⟨h₀, -⟩, -⟩ := hu 1 (one_mem _)
  obtain ⟨k, hk⟩ := exists_power_sum S (fun s => s x) (fun s _ => by rwa [norm_gal]) h₀
  refine ⟨x ^ k, pow_mem hxE k, by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx, ?_⟩
  simp only [map_pow]
  refine hδ.trans (le_trans ?_ hk)
  refine (pow_le_pow_of_le_one (by linarith) (by linarith)
    ((Finset.card_erase_le (a := s₀)).trans hcard)).trans ?_
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => by linarith) fun t ht => ?_
  have ht' := Finset.mem_of_mem_erase ht
  have := hmove (s₀⁻¹ * t) (mul_mem (inv_mem (hS s₀ h₀)) (hS t ht'))
    fun h => Finset.ne_of_mem_erase ht (hsep s₀ h₀ t ht' h).symm
  rw [← norm_gal s₀] at this
  simpa using this
end GlobalTheory.Cyc
