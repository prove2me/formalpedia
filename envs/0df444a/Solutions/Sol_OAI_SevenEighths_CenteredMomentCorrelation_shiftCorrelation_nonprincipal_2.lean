-- Prove2me | solution 2 for OAI.SevenEighths.CenteredMomentCorrelation.shiftCorrelation_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:40.816822+00:00
-- url     : https://prove2.me/submissions/6c8a84aa-7d95-4176-b947-fa29477df8a0

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {F : Type*} [Field F] [Fintype F]

theorem OA2Aux.one_apply_field (x : F) :
    (1 : MulChar F ℂ) x = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst hx
    rw [MulChar.map_zero]
    simp
  · simp [hx, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]

theorem OA2Aux.principal {k : F} (hk : k ≠ 0) :
    shiftCorrelation (1 : MulChar F ℂ) k = (Fintype.card F : ℂ) - 2 := by
  unfold shiftCorrelation
  have h1 : ∀ x : F, (1 : MulChar F ℂ) x * star ((1 : MulChar F ℂ) (x - k)) =
      if x ∈ (Finset.univ \ {0, k} : Finset F) then 1 else 0 := by
    intro x
    rw [OA2Aux.one_apply_field, OA2Aux.one_apply_field]
    by_cases h0 : x = 0
    · subst h0
      simp
    · by_cases h2 : x = k
      · subst h2
        simp
      · have h3 : x - k ≠ 0 := sub_ne_zero.mpr h2
        simp [h0, h2, h3]
  simp_rw [h1]
  rw [Finset.sum_boole]
  have hsub : ({0, k} : Finset F) ⊆ Finset.univ := Finset.subset_univ _
  have hc : (Finset.univ \ {0, k} : Finset F).card = Fintype.card F - 2 := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair (Ne.symm hk)]
    rfl
  have h2le : 2 ≤ Fintype.card F := by
    have := Finset.card_le_univ ({0, k} : Finset F)
    rwa [Finset.card_pair (Ne.symm hk)] at this
  have hf : Finset.filter (fun x : F => x ∈ (Finset.univ \ {0, k} : Finset F)) Finset.univ =
      (Finset.univ \ {0, k} : Finset F) := by
    ext x
    simp
  rw [hf, hc, Nat.cast_sub h2le]
  norm_num

theorem OA2Aux.nonprincipal (χ : MulChar F ℂ) (hχ : χ ≠ 1) {k : F} (hk : k ≠ 0) :
    shiftCorrelation χ k = -1 := by
  unfold shiftCorrelation
  have h1 : ∀ x : F, χ x * star (χ (x - k)) =
      χ (1 + k * (x - k)⁻¹) - (if x = k then 1 else 0) := by
    intro x
    rw [MulChar.star_apply', MulChar.inv_apply', ← map_mul]
    by_cases hx : x = k
    · subst hx
      simp [MulChar.map_zero]
    · have hxk : x - k ≠ 0 := sub_ne_zero.mpr hx
      simp only [hx, if_false, sub_zero]
      congr 1
      field_simp
      ring
  simp_rw [h1]
  rw [Finset.sum_sub_distrib]
  have hbij : Function.Bijective (fun x : F => 1 + k * (x - k)⁻¹) := by
    rw [← Finite.injective_iff_bijective]
    intro x y hxy
    have h2 : k * (x - k)⁻¹ = k * (y - k)⁻¹ := add_left_cancel hxy
    have h3 : (x - k)⁻¹ = (y - k)⁻¹ := mul_left_cancel₀ hk h2
    have h4 : x - k = y - k := inv_injective h3
    exact sub_left_injective h4
  have h5 : ∑ x : F, χ (1 + k * (x - k)⁻¹) = 0 :=
    (Fintype.sum_bijective _ hbij (fun x => χ (1 + k * (x - k)⁻¹)) (fun y => χ y)
      (fun x => rfl)).trans (MulChar.sum_eq_zero_of_ne_one hχ)
  rw [h5]
  simp

theorem solution (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    {k : F} (hk : k ≠ 0) : shiftCorrelation χ k = -1 :=
  OA2Aux.nonprincipal χ hχ hk
