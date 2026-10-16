-- Prove2me | solution 1 for OAI.ShortEgyptian.backwardDifferences_reciprocal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:15:42.738935+00:00
-- url     : https://prove2.me/submissions/02df402d-e428-4584-beb1-f8dbaa22c2a9

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ReciprocalDifferences.lean:L168-L193
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.backwardDifferences_reciprocal_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Theorems.Thm_OAI_ShortEgyptian_reciprocalTerms_shape

-- ---- from OAI.NumberTheory.ShortEgyptian.ReciprocalDifferences ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem reciprocalProduct_shift (as : List ℝ) (x h : ℝ) :
    reciprocalProduct (as.map (· + h)) x = reciprocalProduct as (x + h) := by
  simp only [reciprocalProduct, List.map_map, Function.comp_def]
  congr 2
  funext a
  congr 1
  ring

theorem reciprocalProduct_difference (as : List ℝ) {x h : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) (has : ∀ a ∈ as, 0 ≤ a) :
    reciprocalProduct as x - reciprocalProduct as (x + h) =
      h * ((expandDifference h as).map (fun bs => reciprocalProduct bs x)).sum := by
  induction as with
  | nil => simp [expandDifference]
  | cons a as ih =>
    have ha : 0 ≤ a := has a (by simp)
    have htail := ih (fun b hb => has b (by simp [hb]))
    have hfrac : 1 / (x + a) - 1 / (x + h + a) =
        h * (1 / (x + a) * (1 / (x + (a + h)))) := by
      have h1 : x + a ≠ 0 := by linarith
      have h2 : x + h + a ≠ 0 := by linarith
      have h3 : x + (a + h) ≠ 0 := by linarith
      field_simp
      ring
    simp only [expandDifference, List.map_cons, List.map_map, Function.comp_def,
      List.sum_cons, reciprocalProduct_cons, reciprocalProduct_shift]
    rw [List.sum_map_mul_left]
    linear_combination reciprocalProduct as (x + h) * hfrac + (1 / (x + a)) * htail

theorem reciprocalTerms_difference (ts : List (List ℝ)) {x h : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) (hts : ∀ as ∈ ts, ∀ a ∈ as, 0 ≤ a) :
    (ts.map (fun as => reciprocalProduct as x)).sum -
      (ts.map (fun as => reciprocalProduct as (x + h))).sum =
      h * ((ts.flatMap (expandDifference h)).map (fun bs => reciprocalProduct bs x)).sum := by
  induction ts with
  | nil => simp
  | cons as ts ih =>
    have has := reciprocalProduct_difference as hx hh (hts as (by simp))
    have htail := ih (fun bs hbs => hts bs (by simp [hbs]))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append]
    linarith

theorem backwardDifferences_reciprocal (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    {x : ℝ} (hx : 0 < x) :
    backwardDifferences hs (fun y => 1 / y) x =
      hs.prod * ((reciprocalTerms hs).map (fun as => reciprocalProduct as x)).sum := by
  induction hs generalizing x with
  | nil => simp [backwardDifferences, reciprocalTerms]
  | cons h hs ih =>
    have hh : 0 ≤ h := hhs h (by simp)
    have hhs' : ∀ t ∈ hs, 0 ≤ t := fun t ht => hhs t (by simp [ht])
    have hs' := (reciprocalTerms_shape hs hhs').2
    have heq := reciprocalTerms_difference (reciprocalTerms hs) hx hh
      (fun as has a ha => (hs' as has).2 a ha |>.1)
    simp only [backwardDifferences, reciprocalTerms, List.prod_cons]
    rw [ih hhs' hx, ih hhs' (by linarith)]
    linear_combination hs.prod * heq

theorem reciprocalProduct_bounds (as : List ℝ) {x U V : ℝ}
    (hU : 0 < U) (hUV : U ≤ V)
    (has : ∀ a ∈ as, U ≤ x + a ∧ x + a ≤ V) :
    (1 / V) ^ as.length ≤ reciprocalProduct as x ∧
      reciprocalProduct as x ≤ (1 / U) ^ as.length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ha := has a (by simp)
    have has' : ∀ b ∈ as, U ≤ x + b ∧ x + b ≤ V := fun b hb => has b (by simp [hb])
    obtain ⟨hlo, hhi⟩ := ih has'
    have hV : 0 < V := hU.trans_le hUV
    have hxa : 0 < x + a := hU.trans_le ha.1
    have hl := one_div_le_one_div_of_le hxa ha.2
    have hu := one_div_le_one_div_of_le hU ha.1
    simp only [reciprocalProduct_cons, List.length_cons, pow_succ']
    exact ⟨mul_le_mul hl hlo (by positivity) (by positivity),
      mul_le_mul hu hhi (by linarith [pow_nonneg (le_of_lt (one_div_pos.mpr hV)) as.length]) (by positivity)⟩

theorem backwardDifferences_reciprocal_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {x U V : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x + hs.sum ≤ V) :
    hs.prod * hs.length.factorial * (1 / V) ^ (hs.length + 1) ≤
        backwardDifferences hs (fun y => 1 / y) x ∧
      backwardDifferences hs (fun y => 1 / y) x ≤
        hs.prod * hs.length.factorial * (1 / U) ^ (hs.length + 1) := by
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  have hUV : U ≤ V := by linarith
  have hp : 0 ≤ hs.prod := List.prod_nonneg hhs
  obtain ⟨hlen, hshape⟩ := reciprocalTerms_shape hs hhs
  have hb (as : List ℝ) (has : as ∈ reciprocalTerms hs) :
      (1 / V) ^ (hs.length + 1) ≤ reciprocalProduct as x ∧
        reciprocalProduct as x ≤ (1 / U) ^ (hs.length + 1) := by
    obtain ⟨hal, hap⟩ := hshape as has
    have hh := reciprocalProduct_bounds as (x := x) hU hUV (fun a ha => by
      obtain ⟨ha0, haH⟩ := hap a ha
      constructor <;> linarith)
    simpa only [hal] using hh
  have hlo := List.sum_le_sum (fun as has => (hb as has).1)
  have hhi := List.sum_le_sum (fun as has => (hb as has).2)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, hlen] at hlo hhi
  rw [backwardDifferences_reciprocal hs hhs (hU.trans_le hx)]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlo hp
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhi hp

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.backwardDifferences_reciprocal_bounds := @_root_.OAI.ShortEgyptian.backwardDifferences_reciprocal_bounds
