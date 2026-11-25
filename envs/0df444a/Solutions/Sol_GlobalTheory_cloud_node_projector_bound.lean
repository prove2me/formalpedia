-- Prove2me | solution 1 for GlobalTheory.cloud_node_projector_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:32.244198+00:00
-- url     : https://prove2.me/submissions/d73c6bbf-caa9-4ab5-aabe-baebade4ccc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterLeSuccAndSqSumLePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormEigenLePowMulNormSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasEigenvalueSummand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirResolventCircleBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LevSubspaceMono
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormSumEigenprojectorLeOfResolventBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CloudNodeProjectionNormLowLevel
import Theorems.Thm_GlobalTheory_norm_node_projector_le
import Theorems.Thm_GlobalTheory_norm_sum_eigenprojector_le_of_resolvent_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (n kk : ℕ) (bv : ℝ)
    (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : Fin n → H →ₗ[ℂ] H) (lam : Fin n → ℝ)
    (hfd : FiniteDimensional ℂ VV) (hb : 0 < bv)
    (hsum : ∀ x, ∑ i, p i x = x)
    (hp : ∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = (lam i : ℂ) • p i x)
    (hpos : ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ lam a ∧ lam a ≤ bv / 32) ∧
      (kk ≤ a.val + 1 → bv - bv / 32 ≤ lam a ∧ lam a ≤ 2 * bv + bv / 32))
    (hgap : ∀ a c : Fin n, a ≠ c → 1 ≤ |lam a - lam c|)
    (hcard : (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk)
    (hres : ∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → ∀ x ∈ VV, 13 * bv / 32 * ‖x‖ ≤ ‖ζ • x - T x‖)
    (hT : ∀ x ∈ VV, ‖T x‖ ≤ 3 * bv * ‖x‖) :
    ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ ∧
      ∀ s : Fin n, kk ≤ s.val + 1 → ‖p s x‖ ≤ 3 * (6 * bv) ^ (n - kk) * ‖x‖ := by
  have h1 : ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ := by
    intro x hx
    have hnorm : ∀ i, ‖(lam i : ℂ) - (-((bv / 16 : ℝ) : ℂ))‖ = |lam i + bv / 16| := by
      intro i
      rw [sub_neg_eq_add, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    have := GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound H (Fin n) VV T p (fun i => (lam i : ℂ)) (univ.filter (fun a : Fin n => a.val + 1 < kk))
      (-((bv / 16 : ℝ) : ℂ)) (9 * bv / 16) (32 / (13 * bv)) hfd (by positivity) (by positivity)
      (fun x _ => hsum x) hp ?_ ?_ ?_ x hx
    · have e : 9 * bv / 16 * (32 / (13 * bv)) = 18 / 13 := by field_simp; norm_num
      rwa [e] at this
    · intro i hi
      have := (hpos i).1 (mem_filter.1 hi).2
      rw [hnorm, abs_lt]
      constructor <;> linarith [this.1, this.2]
    · intro i hi
      have hi' : kk ≤ i.val + 1 := by
        by_contra h
        exact hi (mem_filter.2 ⟨mem_univ _, not_le.1 h⟩)
      have := (hpos i).2 hi'
      rw [hnorm, lt_abs]
      left
      linarith [this.1, this.2]
    · intro ζ hζ y hy
      rw [sub_neg_eq_add] at hζ
      have h := hres ζ hζ y hy
      have e : ‖y‖ = 32 / (13 * bv) * (13 * bv / 32 * ‖y‖) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
  intro x hx
  refine ⟨h1 x hx, fun s hs => ?_⟩
  have hsN : s ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1) := mem_filter.2 ⟨mem_univ _, hs⟩
  have := GlobalTheory.norm_node_projector_le H (Fin n) VV T p (fun i => (lam i : ℂ))
    (univ.filter (fun a : Fin n => kk ≤ a.val + 1)) s (6 * bv) 3 hsN (by positivity) hp ?_ ?_ ?_ ?_ x hx
  · rw [card_erase_of_mem hsN, hcard] at this
    have e : n + 1 - kk - 1 = n - kk := by omega
    rwa [e] at this
  · intro y hy
    rw [← hsum y, map_sum]
    exact VV.sum_mem fun i _ => by rw [(hp i y hy).2]; exact VV.smul_mem _ (hp i y hy).1
  · intro i hi
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hgap s i (ne_of_mem_erase hi).symm
  · intro i hi y hy
    have hi' := (hpos i).2 (mem_filter.1 (mem_of_mem_erase hi)).2
    have h2 : |lam i| ≤ 3 * bv := by
      rw [abs_le]; constructor <;> linarith [hi'.1, hi'.2]
    calc ‖T y - (lam i : ℂ) • y‖ ≤ ‖T y‖ + ‖(lam i : ℂ) • y‖ := norm_sub_le _ _
      _ ≤ 3 * bv * ‖y‖ + 3 * bv * ‖y‖ := by
          refine add_le_add (hT y hy) ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = 6 * bv * ‖y‖ := by ring
  · intro y hy
    have h3 := sum_filter_add_sum_filter_not univ (fun a : Fin n => a.val + 1 < kk) (fun i => p i y)
    rw [hsum y] at h3
    simp only [not_lt] at h3
    have h4 : ∑ i ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1), p i y =
        y - ∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y := by
      rw [eq_sub_iff_add_eq, add_comm]; exact h3
    rw [h4]
    have := h1 y hy
    have h5 := norm_sub_le y (∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y)
    linarith [norm_nonneg y]
end GlobalTheory
