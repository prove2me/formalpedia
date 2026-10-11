-- Prove2me | solution 1 for HunterPDE.Sobolev.smooth_compact_dense
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:19:36.956612+00:00
-- url     : https://prove2.me/submissions/2595b2b0-c313-4283-aed8-fe5e4b0f1963
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HunterPDE_Sobolev_smooth_approximation
import Theorems.Thm_HunterPDE_Sobolev_smooth_compact_cutoff_approximation
import Theorems.Thm_HunterPDE_Sobolev_sobolevNorm_sub_triangle

open MeasureTheory HunterPDE.Sobolev

theorem solution {n k : ℕ} (hk : 1 ≤ k) {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsTestFunction Set.univ φ ∧ sobolevNorm k p Set.univ (f - φ) < ε := by
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨g, hg, hgW, hfg⟩ := smooth_approximation hp hptop f hf (ε / 2) hhalf
  obtain ⟨φ, hφ, hφW, hgφ⟩ :=
    smooth_compact_cutoff_approximation hp hptop g hg hgW (ε / 2) hhalf
  refine ⟨φ, hφ, ?_⟩
  calc
    sobolevNorm k p Set.univ (f - φ) ≤
        sobolevNorm k p Set.univ (f - g) + sobolevNorm k p Set.univ (g - φ) :=
      sobolevNorm_sub_triangle hp hptop Set.univ isOpen_univ f g φ hf hgW hφW
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hfg hgφ
    _ = ε := ENNReal.add_halves ε
