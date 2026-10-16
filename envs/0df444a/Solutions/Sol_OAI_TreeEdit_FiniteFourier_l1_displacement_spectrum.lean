-- Prove2me | solution 1 for OAI.TreeEdit.FiniteFourier.l1_displacement_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:01:16.961758+00:00
-- url     : https://prove2.me/submissions/742d0b57-6dcd-4e68-87e9-8c24cefc99f8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/FiniteFourier.lean:L286-L307
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.FiniteFourier.l1_displacement_spectrum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Theorems.Thm_OAI_TreeEdit_FiniteFourier_scalar_spectrum_aux

-- ---- from OAI.Combinatorics.TreeEdit.FiniteFourier ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteFourier

open scoped ComplexConjugate
open RCLike

variable {A : Type*} [Fintype A] [AddCommGroup A]

lemma scalar_spectrum (g : A → ℝ) :
    HasSpectrum (fun z => average (fun x => |g (x + z) - g x|)) := by
  classical
  apply scalar_spectrum_aux (Finset.univ.image g)
  intro x
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

lemma multiplier_eq (χ : AddChar A ℂ) (z : A) :
    multiplier χ z = 2 - 2 * (χ z).re := by
  rw [multiplier, Complex.sq_norm, Complex.normSq_sub]
  norm_num [Complex.normSq_eq_norm_sq, χ.norm_apply]

lemma average_const (c : ℝ) : average (fun _ : A => c) = c := by
  have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [average, hn]

lemma average_le_const {f : A → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) : average f ≤ c := by
  rw [← average_const (A := A) c]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hf x) (by positivity)

lemma average_multiplier (χ : AddChar A ℂ) :
    average (multiplier χ) = if χ = 0 then 0 else 2 := by
  classical
  by_cases hχ : χ = 0
  · subst χ; simp [average]
  · have hs : ∑ z, (χ z).re = 0 := by
      simpa [Complex.re_sum, hχ] using congr_arg Complex.re (χ.sum_eq_ite)
    have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [average, multiplier_eq, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, hχ, hn]

lemma spectrum_total {V : A → ℝ} {H : AddChar A ℂ → ℝ}
    (hH0 : H 0 = 0) (he : ∀ z, V z = ∑ χ, multiplier χ z * H χ) :
    average V = 2 * ∑ χ, H χ := by
  classical
  calc
    average V = ∑ χ, average (multiplier χ) * H χ := by
      simp only [average, he, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 2 * ∑ χ, H χ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [average_multiplier]
      split_ifs with h
      · subst χ; simp [hH0]
      · rfl

lemma scalar_spectrum_bounded (g : A → ℝ) :
    ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧ H 0 = 0 ∧
      (∀ χ, H χ ≤ ∑ x, |g x|) ∧
      ∀ z, average (fun x => |g (x + z) - g x|) = ∑ χ, multiplier χ z * H χ := by
  obtain ⟨H, hH, hH0, he⟩ := scalar_spectrum g
  refine ⟨H, hH, hH0, ?_, he⟩
  have hle : average (fun z => average (fun x => |g (x + z) - g x|)) ≤ 2 * ∑ x, |g x| := by
    apply average_le_const
    intro z
    apply average_le_const
    intro x
    have h1 : |g (x + z)| ≤ ∑ y, |g y| :=
      Finset.single_le_sum (fun y _ => abs_nonneg (g y)) (Finset.mem_univ _)
    have h2 : |g x| ≤ ∑ y, |g y| :=
      Finset.single_le_sum (fun y _ => abs_nonneg (g y)) (Finset.mem_univ _)
    have htri := abs_sub (g (x + z)) (g x)
    linarith
  rw [spectrum_total hH0 he] at hle
  intro χ
  have hsingle : H χ ≤ ∑ ψ, H ψ :=
    Finset.single_le_sum (fun ψ _ => hH ψ) (Finset.mem_univ _)
  linarith

omit [Fintype A] [AddCommGroup A] in
lemma l1_distance_series (v w : RealL1) :
    dist v w = ∑' j : ℕ, |v j - w j| := by
  rw [dist_eq_norm, lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)]
  simp [Real.norm_eq_abs]

omit [Fintype A] [AddCommGroup A] in
lemma l1_coordinate_summable (v : RealL1) : Summable (fun j : ℕ => |v j|) := by
  simpa [Real.norm_eq_abs] using (lp.memℓp v).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)

omit [Fintype A] [AddCommGroup A] in
lemma l1_distance_summable (v w : RealL1) : Summable (fun j : ℕ => |v j - w j|) := by
  simpa [lp.coeFn_sub] using l1_coordinate_summable (v - w)

theorem l1_displacement_spectrum (F : A → RealL1) :
    HasSpectrum (fun z => average (fun x => dist (F (x + z)) (F x))) := by
  classical
  choose H hH hH0 hHb he using fun j : ℕ => scalar_spectrum_bounded (fun x => F x j)
  have hs : Summable (fun j : ℕ => ∑ x, |F x j|) :=
    summable_sum fun x _ => l1_coordinate_summable (F x)
  have hHs (χ : AddChar A ℂ) : Summable (fun j : ℕ => H j χ) :=
    Summable.of_nonneg_of_le (fun j => hH j χ) (fun j => hHb j χ) hs
  refine ⟨fun χ => ∑' j, H j χ, fun χ => tsum_nonneg (fun j => hH j χ), by simp [hH0], ?_⟩
  intro z
  have hd (x : A) : Summable (fun j : ℕ => |F (x + z) j - F x j|) :=
    l1_distance_summable _ _
  calc
    average (fun x => dist (F (x + z)) (F x)) =
        ∑' j : ℕ, average (fun x => |F (x + z) j - F x j|) := by
      simp only [average, l1_distance_series]
      rw [Summable.tsum_mul_left _ (summable_sum fun x _ => hd x),
        Summable.tsum_finsetSum (fun x _ => hd x)]
    _ = ∑' j : ℕ, ∑ χ, multiplier χ z * H j χ := by simp only [he]
    _ = ∑ χ, multiplier χ z * ∑' j : ℕ, H j χ := by
      rw [Summable.tsum_finsetSum (fun χ _ => (hHs χ).mul_left _)]
      simp only [Summable.tsum_mul_left _ (hHs _)]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

end FiniteFourier

namespace FiniteFourier

variable {A : Type*} [Fintype A] [AddCommGroup A]

end FiniteFourier

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.FiniteFourier
attribute [local instance] Classical.propDecidable
open scoped ComplexConjugate
open RCLike


theorem solution : type_of% @_root_.OAI.TreeEdit.FiniteFourier.l1_displacement_spectrum := @_root_.OAI.TreeEdit.FiniteFourier.l1_displacement_spectrum
