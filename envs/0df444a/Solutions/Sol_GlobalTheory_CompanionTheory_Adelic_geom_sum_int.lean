-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.geom_sum_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:37.212775+00:00
-- url     : https://prove2.me/submissions/e84d3bf1-8826-449d-8d83-b04e1745fb0d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GeomSumIntLe
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_geom_sum_int_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic
namespace GlobalTheory.CompanionTheory.Adelic
theorem _root_.solution :
    ∀ (D M : ℕ), 0 < D → 1 ≤ M → ∀ (x₀ C : ℝ), ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) :=
  fun D M hD hM x₀ C => geom_sum_int_le D M hD hM x₀ C
end GlobalTheory.CompanionTheory.Adelic
