-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_character_normalized_logderiv_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:05:08.031982+00:00
-- url     : https://prove2.me/submissions/535733d6-8467-4e28-8fe8-e41eceaa42a6

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrtCharacterNormalized_logderiv
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_character_normalized_zero_count

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


/-- A distance lower bound controls every pole term at once. -/
theorem mrt_character_normalized_logderiv_norm (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : mrtCharacterNormalizedLFunction χ t z ≠ 0) {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ ∈ mrtCharacterNormalizedZeros χ t, η ≤ ‖z - ρ‖) :
    ‖deriv (mrtCharacterNormalizedLFunction χ t) z / mrtCharacterNormalizedLFunction χ t z‖ ≤
      (mrtCharacterLogDerivativeConstant +
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) / η) *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  let S := (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset
  let m : ℂ → ℕ := fun ρ => (analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat
  have hsum : ‖∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) / η := by
    calc
      _ ≤ ∑ ρ ∈ S, ‖(m ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ S, (m ρ : ℝ) / η := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hη
          (hd ρ ((mrtCharacterNormalizedZeros_finite χ hχ t).mem_toFinset.mp hρ))
      _ = _ := by rw [Finset.sum_div]
  have hcount := div_le_div_of_nonneg_right (mrt_character_normalized_zero_count χ hχ t) hη.le
  have herr := mrtCharacterNormalized_logderiv χ hχ t hz hn
  have htri := norm_add_le
    (deriv (mrtCharacterNormalizedLFunction χ t) z / mrtCharacterNormalizedLFunction χ t z -
      ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
    (∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
  rw [sub_add_cancel] at htri
  calc
    _ ≤ mrtCharacterLogDerivativeConstant *
        Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) +
          ((1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) *
            Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4))) / η := by
      exact htri.trans (add_le_add herr (hsum.trans hcount))
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_character_normalized_logderiv_norm := @OAI.TwoPointCorrelations.mrt_character_normalized_logderiv_norm
