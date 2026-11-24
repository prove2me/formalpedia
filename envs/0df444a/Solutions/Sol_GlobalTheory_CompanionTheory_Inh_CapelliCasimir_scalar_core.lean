-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CapelliCasimir.scalar_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:55.386113+00:00
-- url     : https://prove2.me/submissions/f3561732-1b93-4302-a51d-c20c1b4c3fb3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_CasOfCapelliVec
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_rev_coeff
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_rev_eval

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
namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) (ρ μ a : Fin n → ℂ) (b : Fin n → Fin n → ℂ) (r : ℕ → ℂ)
    (e c : ℂ)
    (h : ∀ Y : ℂ, (∏ l, (Y + ρ l)) * e + ∑ i, (∏ l ∈ univ.erase i, (Y + ρ l)) * a i
      + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (∏ l ∈ (univ.erase i).erase j, (Y + ρ l)) * b i j
      + ∑ d ∈ range (n - 2), (Y + c) ^ d * r d = (∏ l, (Y + μ l)) * e) :
    (∑ l, ρ l) * e + ∑ i, a i = (∑ l, μ l) * e ∧
    ((∑ l, ρ l) ^ 2 - ∑ l, ρ l ^ 2) * e + 2 * ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i
      + 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), b i j
      = ((∑ l, μ l) ^ 2 - ∑ l, μ l ^ 2) * e := by
  have key : C e * rev univ ρ + X * ∑ i, C (a i) * rev (univ.erase i) ρ
      + X ^ 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (b i j) * rev ((univ.erase i).erase j) ρ
      + X ^ 3 * ∑ d ∈ range (n - 2), C (r d) * X ^ (n - 3 - d) * (1 + C c * X) ^ d
      = C e * rev univ μ := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := {0}ᶜ) ?_ (Set.finite_singleton (0:ℂ)).infinite_compl
    intro t ht
    have ht : t ≠ 0 := ht
    simp only [Set.mem_setOf_eq, eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_finset_sum,
      eval_one, rev_eval _ _ _ ht, card_univ, Fintype.card_fin]
    have := congrArg (fun z => t ^ n * z) (h t⁻¹)
    simp only [mul_add, mul_sum] at this ⊢
    refine Eq.trans ?_ (this.trans (by ring))
    congr 1
    · congr 1
      · congr 1
        · ring
        · refine sum_congr rfl fun i _ => ?_
          rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
          obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
          have : t ^ n = t * t ^ (n - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [this]; ring
      · refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
        have hij : j ≠ i := (mem_filter.1 hj).2.ne'
        rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ _⟩), card_erase_of_mem (mem_univ _),
          card_univ, Fintype.card_fin]
        have : t ^ n = t ^ 2 * t ^ (n - 1 - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
    · refine sum_congr rfl fun d hd => ?_
      have hd := mem_range.1 hd
      have h1 : t ^ n = t ^ 3 * t ^ (n - 3 - d) * t ^ d := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have h2 : (1 + c * t) = t * (t⁻¹ + c) := by field_simp
      rw [h1, h2, mul_pow]; ring
  have k1 := congrArg (fun p => p.coeff 1) key
  have k2 := congrArg (fun p => p.coeff 2) key
  simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul'] at k1 k2
  have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
  have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
  rw [c1] at k1
  rw [c2] at k2
  simp only [finset_sum_coeff, coeff_C_mul, (rev_coeff _ _).1, (rev_coeff _ _).2.1, le_refl, if_true,
    Nat.sub_self, mul_one] at k1 k2
  norm_num at k1 k2
  constructor
  · linear_combination k1
  · have p1 := (rev_coeff univ ρ).2.2
    have p2 := (rev_coeff univ μ).2.2
    have : ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i = ∑ i, a i * (∑ l, ρ l - ρ i) := by
      refine sum_congr rfl fun i _ => ?_
      rw [sum_erase_eq_sub (mem_univ _), mul_comm]
    rw [this]
    linear_combination 2 * k2 - e * p1 + e * p2
end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
