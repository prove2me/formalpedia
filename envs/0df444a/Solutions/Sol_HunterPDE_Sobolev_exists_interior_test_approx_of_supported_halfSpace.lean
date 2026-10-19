-- Prove2me | solution 1 for HunterPDE.Sobolev.exists_interior_test_approx_of_supported_halfSpace
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T21:05:43.352716+00:00
-- url     : https://prove2.me/submissions/1af81839-82c7-468e-9131-3920e3a53111

import Theorems.Thm_HunterPDE_Sobolev_exists_smooth_approx_with_halfSpace_gap
import Theorems.Thm_HunterPDE_Sobolev_smooth_compact_cutoff_approximation_support
import Theorems.Thm_HunterPDE_Sobolev_sobolevNorm_sub_triangle

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {m k : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hF : HunterPDE.Sobolev.MemW k p Set.univ F)
    (hsupport : ∀ᵐ x ∂volume, x ∉ closedUpperHalfSpace m → F x = 0)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
      HunterPDE.Shared.IsTestFunction (upperHalfSpace m) φ ∧
      HunterPDE.Sobolev.MemW k p Set.univ φ ∧
      HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - φ) < ε := by
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨g, δ, hδ, hg, hgW, hgs, hFg⟩ :=
    HunterPDE.Sobolev.exists_smooth_approx_with_halfSpace_gap
      hp hp' F hF hsupport (ε / 2) hhalf
  obtain ⟨φ, hφ, hφW, hgφ, hφs⟩ :=
    HunterPDE.Sobolev.smooth_compact_cutoff_approximation_support
      hp hp' g hg hgW (ε / 2) hhalf
  refine ⟨φ, ⟨hφ.1, hφ.2.1, ?_⟩, hφW, ?_⟩
  · intro x hx
    exact lt_of_lt_of_le hδ (hgs (hφs hx))
  · calc
      HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - φ) ≤
          HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - g) +
            HunterPDE.Sobolev.sobolevNorm k p Set.univ (g - φ) :=
        HunterPDE.Sobolev.sobolevNorm_sub_triangle hp hp' Set.univ isOpen_univ
          F g φ hF hgW hφW
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hFg hgφ
      _ = ε := ENNReal.add_halves ε
