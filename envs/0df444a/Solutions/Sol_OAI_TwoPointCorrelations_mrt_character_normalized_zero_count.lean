-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_character_normalized_zero_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:58:03.995649+00:00
-- url     : https://prove2.me/submissions/cbede9ec-c6a1-4871-97c6-3c5167d7e88d

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_Erdos970_lem_analytic_zero_factor
import Theorems.Thm_Erdos970_lem_sum_m_rho_bound
import Theorems.Thm_OAI_TwoPointCorrelations_mrtCharacterNormalizedLFunction_norm

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterZeroCount
namespace OAI

/-! Jensen's bound for the total multiplicity in the fixed normalized disk.
This counts actual zeros, with their analytic multiplicities, and will control
the entire logarithmic derivative once a zero-free strip supplies distance. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]

theorem mrt_character_normalized_zero_count (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) :
    (∑ ρ ∈ (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset,
      ((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat : ℝ)) ≤
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  let f := mrtCharacterNormalizedLFunction χ t
  have hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z := by
    intro z _
    exact (mrtCharacterNormalizedLFunction_differentiable χ hχ t).analyticAt z
  have hf0 : f 0 = 1 := mrtCharacterNormalizedLFunction_zero χ t
  have hfactor : ∀ ρ : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      (ρ ∈ Erdos970.zerosetKfR (7 / 8) (by norm_num) f →
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g w) := by
    intro ρ
    by_cases hρ : ρ ∈ Erdos970.zerosetKfR (7 / 8) (by norm_num) f
    · obtain ⟨g, hg, hgne, heq⟩ := Erdos970.lem_analytic_zero_factor
        (15 / 16) (7 / 8) (by norm_num) (by norm_num) (by norm_num) f hf
        (by rw [hf0]; exact one_ne_zero) ρ hρ
      exact ⟨g, hg, hgne, fun _ => heq⟩
    · exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, fun h => (hρ h).elim⟩
  let g : ℂ → ℂ → ℂ := fun ρ => Classical.choose (hfactor ρ)
  have hg : ∀ ρ ∈ Erdos970.zerosetKfR (7 / 8) (by norm_num) f,
      AnalyticAt ℂ (g ρ) ρ ∧ g ρ ρ ≠ 0 ∧
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g ρ w := by
    intro ρ hρ
    exact ⟨(Classical.choose_spec (hfactor ρ)).1,
      (Classical.choose_spec (hfactor ρ)).2.1,
      (Classical.choose_spec (hfactor ρ)).2.2 hρ⟩
  have hK : 1 ≤ mrtCharacterInverseConstant := by
    unfold mrtCharacterInverseConstant
    exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
  have hB : 1 < (2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4) := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have hscale : 1 ≤ (2 * q : ℝ) * mrtCharacterInverseConstant := by nlinarith
    have hm := le_mul_of_one_le_left (show 0 ≤ |t|+4 by positivity) hscale
    linarith [abs_nonneg t]
  exact Erdos970.lem_sum_m_rho_bound
    ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) (15 / 16) (7 / 8) hB
    (by norm_num) (by norm_num) (by norm_num) f hf
    (by rw [hf0]; exact one_ne_zero) hf0 (mrtCharacterNormalizedZeros_finite χ hχ t) g
    (fun z hz => mrtCharacterNormalizedLFunction_norm χ hχ t (hz.trans (by norm_num))) hg


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_character_normalized_zero_count := @OAI.TwoPointCorrelations.mrt_character_normalized_zero_count
