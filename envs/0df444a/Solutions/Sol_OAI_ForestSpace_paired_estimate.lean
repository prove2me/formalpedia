-- Prove2me | solution 1 for OAI.ForestSpace.paired_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:51:34.640252+00:00
-- url     : https://prove2.me/submissions/f27840a6-a5b2-4bbc-b473-26ccc75c28a5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Polar.lean:L125-L156
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.paired_estimate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Theorems.Thm_OAI_ForestSpace_TestVector_paired_correction
import Theorems.Thm_OAI_ForestSpace_exists_raw_test
import Theorems.Thm_OAI_ForestSpace_paired_polar_test

-- ---- from OAI.Analysis.ForestSpace.Completion ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

namespace TestVector
variable {V : Type}
variable [PartialOrder V]
 theorem cut_supported (H : Set V) (u : TestVector V) : SupportedOn (cut H u) H := by
  intro v hv
  simp [hv]

end TestVector

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Polar ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section PolarTests
variable {V : Type} [PartialOrder V]

 theorem exists_head_test (H : Set V) (hH : IsLowerSet H) (x : FullDual V)
    (hx : Annihilates x Hᶜ) {r : ℝ} (hr : r < ‖x‖) :
    ∃ f : TestVector V, SupportedOn f H ∧ ‖f‖ ≤ 1 ∧ r < x (f : J V) := by
  obtain ⟨u,hu,hr⟩ := exists_raw_test x hr
  have he := congrArg (rawRestriction x) (TestVector.cut_add_compl H u)
  have hz := hx (TestVector.cut Hᶜ u) (TestVector.cut_supported Hᶜ u)
  simp only [map_add, rawRestriction_apply, hz, add_zero] at he
  exact ⟨TestVector.cut H u, TestVector.cut_supported H u,
    (TestVector.norm_cut_le H hH u).trans hu, by simpa only [he] using hr⟩

 theorem exists_tail_test (H : Set V) (hH : IsLowerSet H) (x : FullDual V)
    (hx : Annihilates x H) {r : ℝ} (hr : r < ‖x‖) :
    ∃ k : TestVector V, SupportedOn k Hᶜ ∧ ‖k‖ ≤ 1 ∧ r < x (k : J V) := by
  obtain ⟨u,hu,hr⟩ := exists_raw_test x hr
  have he := congrArg (rawRestriction x) (TestVector.cut_add_compl H u)
  have hz := hx (TestVector.cut H u) (TestVector.cut_supported H u)
  simp only [map_add, rawRestriction_apply, hz, zero_add] at he
  exact ⟨TestVector.cut Hᶜ u, TestVector.cut_supported Hᶜ u,
    (TestVector.norm_cut_compl_le H hH u).trans hu, by simpa only [he] using hr⟩

 theorem paired_parameter (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (x y : FullDual V)
    (hx : Annihilates x Hᶜ) (hy : Annihilates y H) (s : ℝ) (hs : 0 < s) :
    (‖x‖ + s * ‖y‖) / Real.sqrt (1 + 12 * s ^ 2) ≤ (‖x+y‖ + ‖x-y‖) / 2 := by
  have hd : 0 < Real.sqrt (1 + 12 * s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_iff₀ hd).mpr
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨f,hf,hf₁,hfx⟩ := exists_head_test H hH x hx (show ‖x‖-ε/2 < ‖x‖ by linarith)
  obtain ⟨k,hk,hk₁,hky⟩ := exists_tail_test H hH y hy
    (show ‖y‖-ε/(2*s) < ‖y‖ by
      have : 0 < ε/(2*s) := by positivity
      linarith)
  obtain ⟨c,hc,hc₁,hp,hm⟩ := TestVector.paired_correction hF hAnc H hH f k hf hk hf₁ hk₁ s hs
  have ht := paired_polar_test H hx hy hf hk hc s (Real.sqrt (1+12*s^2)) hp hm
  have hm' := mul_lt_mul_of_pos_left hky hs
  have he : s * (ε / (2*s)) = ε/2 := by field_simp
  rw [mul_sub, he] at hm'
  linarith

 theorem paired_estimate (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (x y : FullDual V)
    (hx : Annihilates x Hᶜ) (hy : Annihilates y H) :
    Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2 / 12) ≤ (‖x+y‖ + ‖x-y‖) / 2 := by
  by_cases hx0 : x = 0
  · subst x
    simp only [norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), zero_add, zero_sub, norm_neg]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg ‖y‖]
  by_cases hy0 : y = 0
  · subst y
    simp only [norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), zero_div, add_zero, sub_zero]
    rw [Real.sqrt_sq (norm_nonneg _)]
    linarith
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  let s := ‖y‖ / (12 * ‖x‖)
  have hs : 0 < s := by dsimp [s]; positivity
  have hd : 0 < Real.sqrt (1+12*s^2) := Real.sqrt_pos.mpr (by positivity)
  have hh := (div_le_iff₀ hd).mp (paired_parameter hF hAnc H hH x y hx hy s hs)
  have he : (‖x‖+s*‖y‖)^2 = (‖x‖^2+‖y‖^2/12)*(1+12*s^2) := by
    dsimp [s]
    field_simp

  have hh' : (‖x‖+s*‖y‖)^2 ≤ ((‖x+y‖+‖x-y‖)/2 * Real.sqrt (1+12*s^2))^2 :=
    sq_le_sq₀ (by positivity) (by positivity) |>.mpr hh
  rw [he, mul_pow, Real.sq_sqrt (by positivity)] at hh'
  have hden : 0 < 1+12*s^2 := by positivity
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, (mul_le_mul_iff_left₀ hden).mp (by simpa only [mul_comm] using hh')⟩

end PolarTests

section CoordinateCompletion
variable {W : Type} [PartialOrder W]
variable {V : Type} [PartialOrder V]

end CoordinateCompletion

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.paired_estimate := @_root_.OAI.ForestSpace.paired_estimate
