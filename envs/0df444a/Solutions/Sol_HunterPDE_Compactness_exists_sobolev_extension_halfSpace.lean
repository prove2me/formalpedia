-- Prove2me | solution 1 for HunterPDE.Compactness.exists_sobolev_extension_halfSpace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T09:15:09.297767+00:00
-- url     : https://prove2.me/submissions/5e6bdce7-6e23-4b7d-b24b-19157b23a1cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Real_exists_finite_moment_weights
import Theorems.Thm_HunterPDE_Compactness_memW_matching_reflection
import Theorems.Thm_HunterPDE_Compactness_memW_iff_sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution (m k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : HunterPDE.Compactness.MemW k p (HunterPDE.Compactness.upperHalfSpace m) f) :
    ∃ F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
      HunterPDE.Sobolev.MemW k p Set.univ F ∧
        F =ᵐ[volume.restrict (HunterPDE.Compactness.upperHalfSpace m)] f := by
  classical
  let b : Fin (k + 1) → ℝ := fun j => (j : ℝ) + 1
  have hb : ∀ j, 0 < b j := fun j => by dsimp [b]; positivity
  have hv : Function.Injective (fun j : Fin (k + 1) => -b j) := by
    intro i j h
    apply Fin.ext
    have h' : (i : ℝ) = (j : ℝ) := by simpa only [neg_inj, b, add_left_inj] using h
    exact_mod_cast h'
  obtain ⟨c, hc⟩ := Real.exists_finite_moment_weights (k + 1) (fun j => -b j) hv 1
  have hm : ∀ r : ℕ, r ≤ k → ∑ j : Fin (k + 1), c j * (-b j) ^ r = 1 := by
    intro r hr
    simpa only [one_pow] using hc ⟨r, Nat.lt_succ_of_le hr⟩
  let F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun x =>
    if 0 < x (Fin.last m) then f x else
      ∑ j : Fin (k + 1), c j * f
        (WithLp.toLp 2 (Function.update (fun l => x l) (Fin.last m) (-b j * x (Fin.last m))))
  have hF : HunterPDE.Compactness.MemW k p Set.univ F :=
    HunterPDE.Compactness.memW_matching_reflection (Fin.last m) k (k + 1) p hp hp'
      b c hb hm f hf
  refine ⟨F, (HunterPDE.Compactness.memW_iff_sobolev Set.univ F).mp hF, ?_⟩
  have hH : MeasurableSet (HunterPDE.Compactness.upperHalfSpace m) := by
    exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
  apply (ae_restrict_iff' hH).mpr
  exact Filter.Eventually.of_forall fun x hx => if_pos hx
