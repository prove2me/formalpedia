-- Prove2me | solution 1 for OAI.CubicFirstMoment.bounded_large_common_nonzero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:55:47.353456+00:00
-- url     : https://prove2.me/submissions/74de5d9f-0d65-4598-9753-98a592aa8bde
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008
import Definitions.Def_OAIQ096A010
import Theorems.Thm_OAI_CubicFirstMoment_large_common_nonzero_power

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composite residue characters, Chinese remainders and squarefree Gauss norms. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

theorem norm_gauss {b : Eisenstein} (hb : primary b) :
    ‖gauss b‖ = if Squarefree b then 1 else 0 := by
  split_ifs with hs
  · exact norm_gauss_of_squarefree hb hs
  · rw [gauss_eq_zero_of_not_squarefree hb hs, norm_zero]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform exponent saving applied to the actual finite frequency mass. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primary_support_card_le (S : Finset Eisenstein) {U : ℝ} (hU : 0 ≤ U)
    (hS : ∀ s ∈ S, primary s ∧ norm s ≤ U) : (S.card:ℝ) ≤ 18*U := by
  have hsub : S ⊆ nonzeroNormBall U := fun s hs =>
    mem_nonzeroNormBall.mpr ⟨(hS s hs).2,primary_ne_zero (hS s hs).1⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hU)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBoundedTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolute infinite Poisson tail for a bounded coefficient. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma bounded_coefficient_energy (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {N M : ℝ} (hN : 0 ≤ N) (hS : ∀ a ∈ S, primary a ∧ norm a ≤ N)
    (hβ : ∀ a ∈ S, ‖β a‖ ≤ M) :
    (∑ a ∈ S, ‖β a‖^2) ≤ 18*N*M^2 := by
  calc
    _ ≤ ∑ _a ∈ S, M^2 := Finset.sum_le_sum (fun a ha =>
      pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ a ha) 2)
    _ = (S.card:ℝ)*M^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (primary_support_card_le S hN hS) (sq_nonneg M)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonVarianceSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full variance is the exact sum of all common-factor blocks. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma dispersionAmplitude_norm_squarefree {b : Eisenstein} (hb : primary b)
    (hs : Squarefree b) (β : Eisenstein → ℂ) (u : ℝ) :
    ‖dispersionAmplitude β u b‖ = ‖β b‖ := by
  simp only [dispersionAmplitude,norm_mul,norm_normTwist,norm_gauss hb,
    ite_eq_left hs,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCommonPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large common factors use the proved power bound only after their exact
zero mode is removed. No roughness or cancellation of quotient rows is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem bounded_large_common_nonzero_oai (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A M u : ℝ), 2 ≤ Z → 0 < A → (Z/2)^(3/4:ℝ) ≤ A →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖∑ k ∈ (commonRowFactors S).filter (fun k => (Z/2)^(1/4:ℝ) ≤ norm k),
        (commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k-
          commonGramZeroMode S (fun a => star (dispersionAmplitude β u a)) V A k)‖ ≤
        K*A^(2/3:ℝ)*Z^(5/3-1/32:ℝ)*M^2 := by
  obtain ⟨K,hK,hbound⟩ := large_common_nonzero_power
    (δ := 1/4) (by norm_num) (by norm_num) V hV hV'
  refine ⟨18*K,by positivity,?_⟩
  intro S β Z A M u hZ hA hZA hS hβ
  have hZp : 0 < Z := by linarith
  let v : Eisenstein → ℂ := fun a => star (dispersionAmplitude β u a)
  have hv (a : Eisenstein) (ha : a ∈ S) : ‖v a‖ ≤ M := by
    simpa only [v,norm_star,dispersionAmplitude_norm_squarefree (hS a ha).1
      (hS a ha).2.1] using hβ a ha
  have he := bounded_coefficient_energy S v hZp.le
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2.2⟩) hv
  have hb := hbound S v A (Z/2) hA (by linarith) (by convert hZA using 1; norm_num)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.1,
      by nlinarith [(hS a ha).2.2.2]⟩)
  have hpow : (Z/2)^(2/3-(1/4)/8:ℝ) ≤ Z^(2/3-1/32:ℝ) := by
    norm_num
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  calc
    _ ≤ K*A^(2/3:ℝ)*(Z/2)^(2/3-(1/4)/8:ℝ)*∑ a ∈ S, ‖v a‖^2 := hb
    _ ≤ K*A^(2/3:ℝ)*Z^(2/3-1/32:ℝ)*(18*Z*M^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) he
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    _ = (18*K)*A^(2/3:ℝ)*(Z^(2/3-1/32:ℝ)*Z)*M^2 := by ring
    _ = _ := by
      rw [show Z^(2/3-1/32:ℝ)*Z = Z^(5/3-1/32:ℝ) by
        nth_rw 2 [←Real.rpow_one Z]
        rw [←Real.rpow_add hZp]
        congr 1
        ring]

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.bounded_large_common_nonzero_oai := @OAI.CubicFirstMoment.bounded_large_common_nonzero_oai
