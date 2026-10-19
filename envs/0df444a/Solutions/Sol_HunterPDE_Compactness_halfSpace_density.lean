-- Prove2me | solution 1 for HunterPDE.Compactness.halfSpace_density
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T08:44:56.535661+00:00
-- url     : https://prove2.me/submissions/f91d6a86-77ee-4720-b07d-23d2ab552b6e

import Theorems.Thm_HunterPDE_Compactness_exists_sobolev_extension_halfSpace
import Theorems.Thm_HunterPDE_Compactness_sobolevNorm_restrict_le
import Theorems.Thm_HunterPDE_Sobolev_smooth_approximation
import Theorems.Thm_HunterPDE_Sobolev_smooth_compact_cutoff_approximation
import Theorems.Thm_HunterPDE_Sobolev_sobolevNorm_sub_triangle
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal
set_option autoImplicit false

theorem solution (m k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : MemW k p (upperHalfSpace m) f)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace φ ∧
      sobolevNorm k p (upperHalfSpace m) (f - φ) < ε := by
  obtain ⟨F, hF, hFf⟩ := exists_sobolev_extension_halfSpace m k p hp hp' f hf
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨g, hg, hgW, hFg⟩ :=
    HunterPDE.Sobolev.smooth_approximation hp hp' F hF (ε / 2) hhalf
  obtain ⟨φ, hφ, hφW, hgφ⟩ :=
    HunterPDE.Sobolev.smooth_compact_cutoff_approximation hp hp' g hg hgW
      (ε / 2) hhalf
  have hFφ : HunterPDE.Sobolev.MemW k p Set.univ (F - φ) := by
    refine ⟨hF.1.sub hφW.1, ?_⟩
    intro α hα
    obtain ⟨u, hu, hup⟩ := hF.2 α hα
    obtain ⟨v, hv, hvp⟩ := hφW.2 α hα
    exact ⟨u - v, hu.sub hv, hup.sub hvp⟩
  refine ⟨φ, ⟨hφ.1.contDiffOn, tsupport φ, hφ.2.1, ?_⟩, ?_⟩
  · intro x _ hx
    exact image_eq_zero_of_notMem_tsupport hx
  · have hH : IsOpen (upperHalfSpace m) :=
      isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
    calc
      sobolevNorm k p (upperHalfSpace m) (f - φ) ≤
          HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - φ) :=
        sobolevNorm_restrict_le _ hH _ _ hFφ
          (hFf.symm.sub (Filter.Eventually.of_forall fun _ => rfl))
      _ ≤ HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - g) +
          HunterPDE.Sobolev.sobolevNorm k p Set.univ (g - φ) :=
        HunterPDE.Sobolev.sobolevNorm_sub_triangle hp hp' Set.univ isOpen_univ
          F g φ hF hgW hφW
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hFg hgφ
      _ = ε := ENNReal.add_halves ε
