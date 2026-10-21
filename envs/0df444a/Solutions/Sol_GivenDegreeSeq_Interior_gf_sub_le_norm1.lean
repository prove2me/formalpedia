-- Prove2me | solution 1 for GivenDegreeSeq.Interior.gf_sub_le_norm1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:25:48.566767+00:00
-- url     : https://prove2.me/submissions/a8bd999d-cb0a-4347-a0ba-32877f7637b4

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_DPrime

set_option autoImplicit false
open GivenDegreeSeq.Interior MeasureTheory intervalIntegral

lemma gdi_int_anti (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1)) (a b : ℝ)
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    IntervalIntegrable f volume a b := by
  apply AntitoneOn.intervalIntegrable
  intro x hx y hy hxy
  have h01 : Set.uIcc a b ⊆ Set.Icc (0:ℝ) 1 := Set.uIcc_subset_Icc ha hb
  exact hf (h01 hx) (h01 hy) hxy

lemma gdi_min_anti (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1)) (x : ℝ) :
    AntitoneOn (fun y => min (f y) x) (Set.Icc 0 1) := by
  intro a ha b hb hab
  exact min_le_min_right _ (hf ha hb hab)

theorem solution (f f' : ℝ → ℝ) (hf : InDprime f) (hf' : InDprime f') :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |Gf f x - Gf f' x| ≤ norm1' (f - f') := by
  intro x hx
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have I := fun a b ha hb => gdi_int_anti f hf.1 a b ha hb
  have I' := fun a b ha hb => gdi_int_anti f' hf'.1 a b ha hb
  have M := fun a b ha hb => gdi_int_anti _ (gdi_min_anti f hf.1 x) a b ha hb
  have M' := fun a b ha hb => gdi_int_anti _ (gdi_min_anti f' hf'.1 x) a b ha hb
  set D : ℝ → ℝ := fun y => |f y - f' y| with hD
  have ID : ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → IntervalIntegrable D volume a b :=
    fun a b ha hb => ((I a b ha hb).sub (I' a b ha hb)).abs
  have e1 : Gf f x - Gf f' x =
      (∫ y in x..1, (min (f y) x - min (f' y) x)) - ∫ y in (0:ℝ)..x, (f y - f' y) := by
    unfold Gf
    rw [integral_sub (M x 1 hx h1) (M' x 1 hx h1), integral_sub (I 0 x h0 hx) (I' 0 x h0 hx)]
    ring
  have b1 : |∫ y in x..1, (min (f y) x - min (f' y) x)| ≤ ∫ y in x..1, D y := by
    refine (abs_integral_le_integral_abs hx.2).trans ?_
    refine integral_mono_on hx.2 (((M x 1 hx h1).sub (M' x 1 hx h1)).abs) (ID x 1 hx h1) ?_
    intro y _
    have := abs_min_sub_min_le_max (f y) x (f' y) x
    simpa [hD] using this
  have b2 : |∫ y in (0:ℝ)..x, (f y - f' y)| ≤ ∫ y in (0:ℝ)..x, D y :=
    abs_integral_le_integral_abs hx.1
  have hsum : (∫ y in (0:ℝ)..x, D y) + ∫ y in x..1, D y = ∫ y in (0:ℝ)..1, D y :=
    integral_add_adjacent_intervals (ID 0 x h0 hx) (ID x 1 hx h1)
  have hnn : 0 ≤ ∫ y in (0:ℝ)..1, D y :=
    integral_nonneg zero_le_one (fun y _ => abs_nonneg _)
  unfold norm1'
  have e2 : (∫ y in (0:ℝ)..1, |(f - f') y|) = ∫ y in (0:ℝ)..1, D y := rfl
  rw [e1, e2]
  have := abs_nonneg ((f - f') 0)
  have := abs_nonneg ((f - f') 1)
  calc _ ≤ |∫ y in x..1, (min (f y) x - min (f' y) x)| + |∫ y in (0:ℝ)..x, (f y - f' y)| :=
        abs_sub _ _
    _ ≤ _ := by linarith
