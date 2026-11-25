-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_of_capelli_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:54:09.521221+00:00
-- url     : https://prove2.me/submissions/8f5dec9f-4396-40a5-a5b7-1a983f1e6017

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_CasOfCapelliVec
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_scalar_core
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_sq_sub_cas
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_cvalR_eq
import Theorems.Thm_GlobalTheory_qdet_top_three_orders


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Inh GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Polynomial
open Formalism.REAL
namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
theorem _root_.solution : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (v : V), GlRel E → (∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v) → Cas E v = ((cvalR ε lam : ℝ) : ℂ) • v := by
  intro n ε M _ _ E mu v hE h
  rw [cvalR_eq]
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders (Module.End ℂ M) n E
  by_cases hn : 2 ≤ n
  swap
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp [Cas]
    · have h0 := h 0
      rw [hR] at h0
      have h1 : E 0 0 v = (mu 0 : ℂ) • v := by
        simpa [Formalism.QuantumDeterminants.capP, Finset.filter_singleton] using h0
      simp [Cas, h1, sq, mul_smul]
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun φ : Module.Dual ℂ M =>
    scalar_core n hn ρ (fun s => (mu s : ℂ)) (fun i => φ (E i i v))
      (fun i j => φ ((E i i * E j j - E j i * E i j) v)) (fun d => φ (Rm d v)) (φ v)
      (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 := h Y
        rw [hR] at h1
        have h2 := congrArg φ h1
        simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          Module.End.one_apply, map_add, map_sum, map_smul, smul_eq_mul, add_sub_assoc,
          Formalism.QuantumDeterminants.capP] at h2
        exact h2)
  have e1 : (∑ i, E i i) v = (∑ l, (mu l : ℂ)) • v := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have := (core φ).1
    rw [hρ0] at this
    simp only [LinearMap.sum_apply, map_sub, map_sum, map_smul, smul_eq_mul]
    linear_combination this
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have h2 := (core φ).2
  have h3 := congrArg (fun T : Module.End ℂ M => φ (T v)) (sq_sub_cas E hE)
  rw [LinearMap.sub_apply, Module.End.mul_apply, e1, map_smul, e1, LinearMap.sub_apply] at h3
  simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sub φ, map_sum, map_smul,
    smul_eq_mul] at h3 h2 ⊢
  have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * φ (E i i v)
      = - (2 * ∑ i, (0 - ρ i) * φ (E i i v)) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [hρ]; ring
  rw [h5] at h3
  linear_combination -h3 - h2
end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
