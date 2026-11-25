-- Prove2me | solution 1 for Newton.exists_dual_pair_for_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:44:16.389029+00:00
-- url     : https://prove2.me/submissions/a47ecb2b-13ea-4bad-a968-479d392ae59a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Theorems.Thm_Newton_dual_candidate_memLp
import Theorems.Thm_Newton_dual_candidate_pairing_eq

set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Newton
theorem _root_.solution
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ) (hf_norm : (eLpNorm f p μ).toReal = 1) :
    ∃ g : α → ℝ,
      MemLp g q μ ∧
      (eLpNorm g q μ).toReal = 1 ∧
      Integrable (fun x => f x * g x) μ ∧
      (∫ x, f x * g x ∂μ) = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  -- Build the Hölder-dual candidate using the standard power/sign recipe.
  set pr : ℝ := p.toReal with hpr
  set qr : ℝ := q.toReal with hqr
  set g : α → ℝ :=
    fun x => Real.sign (f x) * |f x| ^ (pr - 1) with hg_def
  have hp_pos : 0 < p := lt_trans (by simp) hp
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have hp_ne_top : p ≠ ∞ := by
    cases hpq with
    | inl h =>
        rcases h with ⟨hp_eq, _⟩
        exact ((by simp [hp_eq] at hp) : False).elim
    | inr h =>
        cases h with
        | inl h' =>
            rcases h' with ⟨hp_eq, hq_eq⟩
            exact ((by simp [hq_eq] at hq) : False).elim
        | inr h' =>
            rcases h' with ⟨_, hp_top, _, _, _⟩
            exact ne_of_lt hp_top
  have h_pr_pos : 0 < pr := by
    simpa [pr] using ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have h_qr_pos : 0 < qr := by
    have hq_pos : 0 < q := lt_trans (by simp) hq
    have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
    have hq_ne_top : q ≠ ∞ := by
      cases hpq with
      | inl h =>
          rcases h with ⟨hp_eq, hq_eq⟩
          exact ((by simp [hp_eq] at hp) : False).elim
      | inr h =>
          cases h with
          | inl h' =>
              rcases h' with ⟨hp_eq, hq_eq⟩
              exact by simp [hq_eq]
          | inr h' =>
              rcases h' with ⟨_, _, _, hq_top, _⟩
              exact ne_of_lt hq_top
    simpa [qr] using ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hpq_sum : 1 / p + 1 / q = 1 := by
    obtain ⟨hp_eq, _⟩ | h := hpq
    · have : False := by simp [hp_eq] at hp
      exact (False.elim this : 1 / p + 1 / q = 1)
    · obtain ⟨hp_eq, hq_eq⟩ | h := h
      · have : False := by simp [hq_eq] at hq
        exact (False.elim this : 1 / p + 1 / q = 1)
      · rcases h with ⟨_, _, _, _, hpq_sum⟩
        exact hpq_sum
  have p_inv_add : p⁻¹ + q⁻¹ = 1 := by simpa [one_div] using hpq_sum
  haveI : ENNReal.HolderTriple p q 1 :=
    ⟨by simp [p_inv_add, inv_one]⟩
  have hg_mem : MemLp g q μ := by
    -- Show that the constructed `g` belongs to `L^q`.
    simpa [g, hg_def, pr, hpr]
      using dual_candidate_memLp (μ := μ) (p := p) (q := q) hp hq hpq hf
  have hg_integrable : Integrable (fun x => f x * g x) μ :=
    MeasureTheory.MemLp.integrable_mul (p := p) (q := q) (μ := μ)
      (f := fun x => f x) (g := fun x => g x) hf hg_mem
  obtain ⟨hg_equality, hg_norm_one⟩ :=
    dual_candidate_pairing_eq (μ := μ) (p := p) (q := q) hp hq hpq hf hf_norm
  refine ⟨g, hg_mem, hg_norm_one, hg_integrable, ?_⟩
  exact hg_equality
end Newton
