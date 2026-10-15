-- Prove2me | solution 1 for HunterPDE.Compactness.halfSpace_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T08:37:28.258565+00:00
-- url     : https://prove2.me/submissions/58af37db-5f54-487c-b7f0-32406e35ac1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HunterPDE_Compactness_memW_evenReflection
import Theorems.Thm_HunterPDE_Compactness_eLpNorm_weakDeriv_evenReflection_le
import Mathlib.Tactic.Positivity

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution (m : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ∃ (C : ℝ≥0) (E : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin (m + 1)) → ℝ),
      (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          E (a • f + b • g) =ᵐ[volume] a • E f + b • E g) ∧
      ∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemW 1 p Set.univ (E f) ∧
        E f =ᵐ[volume.restrict (upperHalfSpace m)] f ∧
        sobolevNorm 1 p Set.univ (E f) ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f := by
  classical
  let R : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun x => WithLp.toLp 2 (fun i => if i = Fin.last m then |x i| else x i)
  let E := fun f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ => fun x => f (R x)
  refine ⟨2, E, ?_, ?_⟩
  · intro f g _ _ a b
    exact Filter.Eventually.of_forall (fun _ => rfl)
  intro f hf
  refine ⟨memW_evenReflection m p hp f hf, ?_, ?_⟩
  · apply (ae_restrict_mem (by
      exact (isOpen_lt continuous_const
        (EuclideanSpace.proj (Fin.last m)).continuous).measurableSet)).mono
    intro x hx
    have hR : R x = x := by
      ext i
      change (if i = Fin.last m then |x i| else x i) = x i
      split_ifs with hi
      · subst i
        exact abs_of_pos hx
      · rfl
    change f (R x) = f x
    rw [hR]
  have hcomp : ∀ α ∈ multiIndicesLe (m + 1) 1,
      eLpNorm (HunterPDE.Shared.weakDeriv Set.univ α (E f)) p (volume.restrict Set.univ) ≤
        2 * eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) α f)
          p (volume.restrict (upperHalfSpace m)) := by
    intro α hα
    exact eLpNorm_weakDeriv_evenReflection_le m p hp f hf α hα
  change sobolevNorm 1 p Set.univ (E f) ≤ 2 * sobolevNorm 1 p (upperHalfSpace m) f
  by_cases htop : p = ∞
  · subst p
    simp only [sobolevNorm, ↓reduceIte]
    apply Finset.sup_le
    intro α hα
    exact (hcomp α hα).trans (mul_le_mul_right (Finset.le_sup hα) (2 : ℝ≥0∞))
  have hpos : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (by simp) hp)) htop
  simp only [sobolevNorm, if_neg htop]
  calc
    _ ≤ (∑ α ∈ multiIndicesLe (m + 1) 1,
        (2 * eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) α f) p
          (volume.restrict (upperHalfSpace m))) ^ p.toReal) ^ (1 / p.toReal) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact Finset.sum_le_sum (fun α hα => ENNReal.rpow_le_rpow (hcomp α hα) hpos.le)
    _ = 2 * (∑ α ∈ multiIndicesLe (m + 1) 1,
        eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) α f) p
          (volume.restrict (upperHalfSpace m)) ^ p.toReal) ^ (1 / p.toReal) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hpos.le]
      rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_mul, mul_one_div_cancel hpos.ne', ENNReal.rpow_one]
