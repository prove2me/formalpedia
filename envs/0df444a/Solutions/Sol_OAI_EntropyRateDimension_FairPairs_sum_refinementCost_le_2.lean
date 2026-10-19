-- Prove2me | solution 2 for OAI.EntropyRateDimension.FairPairs.sum_refinementCost_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:53:57.034252+00:00
-- url     : https://prove2.me/submissions/a1b0c485-d25f-47a0-b3b9-a01f14df3262

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/SumsetBound.lean:L207-L251
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FairPairs.sum_refinementCost_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Theorems.Thm_OAI_EntropyRateDimension_FairPairs_geometric_fine_scale_bound

-- ---- from OAI.MeasureTheory.SelfSimilar.FairPairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

theorem edge_mem_left {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.1 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).1

theorem edge_mem_right {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.2 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).2

theorem incident_sum {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ∑ x ∈ ν.support, incident w x = ∑ e, w e := by
  classical
  simp only [incident]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, edge_mem_left e, edge_mem_right e, ite_true]
  ring

theorem feasible_zero (ν : Law) (ℓ : ℤ) : Feasible (ν := ν) (ℓ := ℓ) (fun _ => 0) := by
  constructor
  · simp
  · intro x hx
    simpa [incident] using (ν.prob_pos x hx).le

theorem total_le_one {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ 1 := by
  rw [← incident_sum w, ← ν.prob_sum]
  exact Finset.sum_le_sum hw.2

theorem totals_bddAbove (ν : Law) (ℓ : ℤ) :
    BddAbove {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t} := by
  refine ⟨1, ?_⟩
  rintro t ⟨w, hw, rfl⟩
  exact total_le_one hw

theorem capacity_nonneg (ν : Law) (ℓ : ℤ) : 0 ≤ capacity ν ℓ := by
  apply le_csSup (totals_bddAbove ν ℓ)
  exact ⟨(fun _ => 0), feasible_zero ν ℓ, by simp⟩

end FairPairs

end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.SumsetBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uβ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FairPairs

open FiniteEntropy

theorem dyadic_upper_eq (ℓ : ℤ) : (2 : ℝ)^(1-ℓ) = 2*(2 : ℝ)^(-ℓ) := by
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]

theorem band_scale_sum (ρ : ℝ) (hρ : 0 < ρ) (ℓ : ℤ) (J : ℕ) :
    (∑ h ∈ (Finset.range J).filter (fun h => (2 : ℝ)^(-ℓ) ≤ ρ/4^h),
      (2 : ℝ)^(1-ℓ)/(ρ/4^h)) ≤ if (2 : ℝ)^(-ℓ) ≤ ρ then 8/3 else 0 := by
  classical
  let s := (Finset.range J).filter (fun h => (2 : ℝ)^(-ℓ) ≤ ρ/4^h)
  have hpow : ∀ h : ℕ, (0 : ℝ) < 4^h := fun h => pow_pos (by norm_num) h
  have hs : ∀ h ∈ s, ((2 : ℝ)^(1-ℓ)/ρ)*4^h ≤ 2 := by
    intro h hh
    have he := (le_div_iff₀ (hpow h)).mp (Finset.mem_filter.mp hh).2
    rw [dyadic_upper_eq]
    have he' : (2*(2 : ℝ)^(-ℓ)*4^h)/ρ ≤ 2 :=
      (div_le_iff₀ hρ).mpr (by nlinarith)
    convert he' using 1; ring
  have hgeom := geometric_fine_scale_bound s
    (div_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le hρ.le) hs
  have heq : (∑ h ∈ s, (2 : ℝ)^(1-ℓ)/(ρ/4^h)) =
      ∑ h ∈ s, ((2 : ℝ)^(1-ℓ)/ρ)*4^h := by
    apply Finset.sum_congr rfl
    intro h _
    field_simp
  change (∑ h ∈ s, _) ≤ _
  rw [heq]
  by_cases hℓ : (2 : ℝ)^(-ℓ) ≤ ρ
  · rw [ite_eq_left hℓ]
    exact hgeom
  · rw [ite_eq_right hℓ]
    have hempty : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro h hh
      have he := (le_div_iff₀ (hpow h)).mp (Finset.mem_filter.mp hh).2
      have hone : (1 : ℝ) ≤ 4^h := one_le_pow₀ (by norm_num)
      have hlower : (2 : ℝ)^(-ℓ) ≤ (2 : ℝ)^(-ℓ)*4^h :=
        le_mul_of_one_le_right (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le hone
      exact hℓ (hlower.trans he)
    simp only [hempty, Finset.sum_empty, le_refl]

theorem sum_refinementCost_le (ν : Law) (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (J : ℕ) :
    (∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h)) ≤
      60000*k^4*Real.log 2 * ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ),
        capacity ν ℓ := by
  classical
  let C : ℝ := 352*k^4*Real.log 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : (∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h)) =
      C * ∑ ℓ ∈ ν.bandSupport, capacity ν ℓ *
        ∑ h ∈ (Finset.range J).filter (fun h => (2 : ℝ)^(-ℓ) ≤ ρ/4^h),
          (2 : ℝ)^(1-ℓ)/(ρ/4^h) := by
    simp only [Law.refinementCost, Law.bandCost, Finset.sum_filter, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ℓ _
    apply Finset.sum_congr rfl
    intro h _
    dsimp only [C]
    split_ifs <;> ring
  rw [he]
  have hpoint := Finset.sum_le_sum (s := ν.bandSupport) (fun ℓ _ =>
    mul_le_mul_of_nonneg_left (band_scale_sum ρ hρ ℓ J) (capacity_nonneg ν ℓ))
  calc
    _ ≤ C * ∑ ℓ ∈ ν.bandSupport, capacity ν ℓ *
        (if (2 : ℝ)^(-ℓ) ≤ ρ then 8/3 else 0) := mul_le_mul_of_nonneg_left hpoint hC
    _ = (C*(8/3)) * ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ ρ), capacity ν ℓ := by
      simp only [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ _
      split_ifs <;> ring
    _ ≤ (60000*k^4*Real.log 2) *
        ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ ρ), capacity ν ℓ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun ℓ _ => capacity_nonneg ν ℓ))
      dsimp only [C]
      have hn : 0 ≤ (k : ℝ)^4*Real.log 2 := by positivity
      nlinarith
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ℓ hℓ
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hℓ).1,
          (Finset.mem_filter.mp hℓ).2.trans (by linarith)⟩
      · intro ℓ _ _
        exact capacity_nonneg ν ℓ

end FairPairs

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.FairPairs.sum_refinementCost_le := @_root_.OAI.EntropyRateDimension.FairPairs.sum_refinementCost_le
