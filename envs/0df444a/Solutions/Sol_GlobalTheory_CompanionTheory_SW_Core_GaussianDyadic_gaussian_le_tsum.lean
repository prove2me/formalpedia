-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.gaussian_le_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:37.482968+00:00
-- url     : https://prove2.me/submissions/ec2f9cf2-c24f-4711-a33d-651b41733ac2

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_exists_dyadic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
theorem _root_.solution {X : Type} (c t : ℝ) (hc : 0 < c) (ht : 0 < t) (s : X → ℝ) (p : X → Prop)
    (hs : ∀ x, 0 ≤ s x) (x : X) :
    Set.indicator {x | p x} (fun x => ENNReal.ofReal (Real.exp (-(c * t * s x ^ 2)))) x ≤
      ∑' j : ℕ, ENNReal.ofReal (wt c j) *
        Set.indicator {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  by_cases hp : p x
  · have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    obtain ⟨j, hj, hexp⟩ := exists_dyadic (c := c) (u := Real.sqrt t * s x) hc
      (mul_nonneg hq.le (hs x))
    have hmem : x ∈ {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t} :=
      ⟨hp, by rw [le_div_iff₀ hq, mul_comm]; exact hj⟩
    have heq : c * (Real.sqrt t * s x) ^ 2 = c * t * s x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht.le]; ring
    rw [heq] at hexp
    rw [Set.indicator_of_mem (show x ∈ {x | p x} from hp)]
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem hmem, mul_one]
    exact ENNReal.ofReal_le_ofReal hexp
  · rw [Set.indicator_of_notMem (show x ∉ {x | p x} from hp)]
    exact zero_le
end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
