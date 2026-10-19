-- Prove2me | solution 2 for OAI.GaussianPropeller.Reduction.scoreMax_recentered
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:45:30.302605+00:00
-- url     : https://prove2.me/submissions/890ca8ab-5b81-49f8-b18e-5d842c025bdf

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Deletion.lean:L100-L130
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.scoreMax_recentered. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

-- ---- from OAI.Probability.GaussianPropeller.Dual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

theorem le_scoreMax (v : Fin k → Space d) (i : Fin k) (x : Space d) :
    ⟪v i, x⟫ ≤ scoreMax v x := by
  exact Finset.le_sup' (fun j => ⟪v j, x⟫) (Finset.mem_univ i)

theorem scoreMax_le_iff (v : Fin k → Space d) (x : Space d) (b : ℝ) :
    scoreMax v x ≤ b ↔ ∀ i, ⟪v i, x⟫ ≤ b := by
  simp only [scoreMax, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

end Reduction

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Deletion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open scoped RealInnerProductSpace

namespace GaussianPropeller.Reduction

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
lemma sum_erase_zero (z : Fin k → Space d) (hz : ∑ j, z j = 0) (i : Fin k) :
    ∑ j ∈ Finset.univ.erase i, z j = -z i := by
  classical
  have hh := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  rw [hz] at hh
  exact eq_neg_of_add_eq_zero_left hh

omit [NeZero k] in
lemma sum_erased_centered (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ∑ j ∈ Finset.univ.erase i, (z j + ((k:ℝ)-1)⁻¹ • z i) = 0 := by
  classical
  have hk' : (k:ℝ)-1 ≠ 0 := by exact_mod_cast (show (k:ℤ)-1 ≠ 0 by omega)
  rw [Finset.sum_add_distrib, sum_erase_zero z hz i,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp only [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
    mul_inv_cancel₀ hk', one_smul, neg_add_cancel]

lemma scoreMax_recentered (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) (x : Space d) :
    scoreMax (recentered z i).ofLp x = omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
  classical
  let f : Fin k → ℝ := fun j => ⟪z j + ((k:ℝ)-1)⁻¹ • z i,x⟫
  have hsum : ∑ j ∈ Finset.univ.erase i, f j = 0 := by
    rw [← sum_inner, sum_erased_centered hk z hz i, inner_zero_left]
  have hnon : 0 ≤ (Finset.univ.erase i).sup' (erase_univ_nonempty hk i) f := by
    by_contra! hn
    have hh : ∑ j ∈ Finset.univ.erase i, f j < 0 := Finset.sum_neg
      (fun j hj => (Finset.le_sup' f hj).trans_lt hn) (erase_univ_nonempty hk i)
    linarith
  have hex : (Finset.univ.erase i).sup' (erase_univ_nonempty hk i) f =
      omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
    dsimp only [omittedMax, f]
    simp_rw [inner_add_left]
    exact (Finset.sup'_add _ _ _ _).symm
  rw [← hex]
  apply le_antisymm
  · apply (scoreMax_le_iff _ _ _).mpr
    intro j
    change ⟪if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i,x⟫ ≤ _
    by_cases hji : j = i
    · simpa only [ite_eq_left hji, inner_zero_left] using hnon
    · rw [ite_eq_right hji]
      exact Finset.le_sup' f (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
  · apply (Finset.sup'_le_iff _ _).mpr
    intro j hj
    have hh := le_scoreMax (recentered z i).ofLp j x
    change ⟪if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i,x⟫ ≤ _ at hh
    simpa only [ite_eq_right (Finset.ne_of_mem_erase hj)] using hh

end GaussianPropeller.Reduction

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.scoreMax_recentered := @_root_.OAI.GaussianPropeller.Reduction.scoreMax_recentered
