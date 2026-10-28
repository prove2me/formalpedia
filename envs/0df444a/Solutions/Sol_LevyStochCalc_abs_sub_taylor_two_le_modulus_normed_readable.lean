-- Prove2me | solution 1 for LevyStochCalc.abs_sub_taylor_two_le_modulus_normed_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:10.985704+00:00
-- url     : https://prove2.me/submissions/5d6b5146-8b55-410d-afe2-edb83f2ea266

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus
import Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le_modulus_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- **Second-order Taylor on a normed space against an oscillation bound.** The remainder is
controlled by the oscillation of the second derivative on the segment joining the two points. -/
theorem solution {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z) {x y : E}
    (hM : ∀ z ∈ segment ℝ x y, ‖f'' z - f'' x‖ ≤ M) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2| ≤ M * ‖y - x‖ ^ 2 := by
  set v : E := y - x with hv
  have hseg : ∀ t : ℝ, HasDerivAt (fun r : ℝ => x + r • v) v t := fun t => by
    have h := ((hasDerivAt_id t).smul_const v).const_add x
    simpa using h
  have hg : ∀ t : ℝ, HasDerivAt (fun r : ℝ => f (x + r • v)) (f' (x + t • v) v) t := fun t =>
    (hf (x + t • v)).comp_hasDerivAt t (hseg t)
  have hg' : ∀ t : ℝ,
      HasDerivAt (fun r : ℝ => f' (x + r • v) v) (f'' (x + t • v) v v) t := fun t => by
    have hap : HasFDerivAt (fun z : E => f' z v)
        ((ContinuousLinearMap.apply ℝ ℝ v).comp (f'' (x + t • v))) (x + t • v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp _ (hf' (x + t • v))
    exact hap.comp_hasDerivAt t (hseg t)
  have hosc : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      |f'' (x + u • v) v v - f'' (x + (0 : ℝ) • v) v v| ≤ M * ‖v‖ ^ 2 := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hmem : x + u • v ∈ segment ℝ x y := by
      rw [segment_eq_image' ℝ x y]
      exact ⟨u, hu, rfl⟩
    have hsub : f'' (x + u • v) v v - f'' (x + (0 : ℝ) • v) v v
        = (f'' (x + u • v) - f'' x) v v := by simp
    have hbd : ‖(f'' (x + u • v) - f'' x) v v‖
        ≤ ‖f'' (x + u • v) - f'' x‖ * ‖v‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm₂ _ v v
    calc |f'' (x + u • v) v v - f'' (x + (0 : ℝ) • v) v v|
        = ‖(f'' (x + u • v) - f'' x) v v‖ := by rw [hsub]; exact (Real.norm_eq_abs _).symm
      _ ≤ ‖f'' (x + u • v) - f'' x‖ * ‖v‖ * ‖v‖ := hbd
      _ ≤ M * ‖v‖ * ‖v‖ := by gcongr; exact hM _ hmem
      _ = M * ‖v‖ ^ 2 := by ring
  have hmain := LevyStochCalc.abs_sub_taylor_two_le_modulus_readable (f := fun r : ℝ => f (x + r • v))
    (f' := fun r : ℝ => f' (x + r • v) v) (f'' := fun r : ℝ => f'' (x + r • v) v v)
    (M := M * ‖v‖ ^ 2) (by positivity) hg hg' (x := 0) (y := 1) hosc
  simpa [hv] using hmain
