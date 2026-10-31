-- Prove2me | solution 1 for OAI.CubicFirstMoment.low_localized_height_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:40:07.133892+00:00
-- url     : https://prove2.me/submissions/66712c62-fb27-40e2-b6fc-20be39af4536

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015
import Theorems.Thm_OAI_CubicFirstMoment_ProfileControl_low_variance_remainder_height_log_saving
import Theorems.Thm_OAI_CubicFirstMoment_low_far_logCell_integrated_bound

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_FrequencyGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime, squarefree and mixed frequency Gauss evaluation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mixedFrequencyGauss_zero {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hne : a ≠ b) : mixedFrequencyGauss a b 0 = 0 := by
  rw [mixedFrequencyGauss_squarefree ha hb hsa hsb hab]
  by_cases ha1 : a = 1
  · have hb1 : b ≠ 1 := fun hb1 => hne (ha1.trans hb1.symm)
    have hnc : ¬ IsCoprime b 0 := fun hc =>
      hb1 (primary_unit_eq_one (isCoprime_zero_right.mp hc) hb)
    rw [cubicSymbol_eq_zero_of_not_isCoprime hb hnc]
    simp
  · have hnc : ¬ IsCoprime a 0 := fun hc =>
      ha1 (primary_unit_eq_one (isCoprime_zero_right.mp hc) ha)
    rw [cubicSymbol_eq_zero_of_not_isCoprime ha hnc]
    simp

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal character Gram kernel and normalized radial Poisson expansion. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

noncomputable section
open Filter
open scoped ContDiff

namespace CubicFirstMoment

lemma norm_gramGauss_scalar {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b) :
    ‖gauss a * star (gauss b)‖ = 1 := by
  rw [norm_mul, norm_star, norm_gauss_of_squarefree ha hsa,
    norm_gauss_of_squarefree hb hsb, one_mul]

lemma gramDualTerm_zero {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hne : a ≠ b) (W : ℝ → ℂ) (Z : ℝ) :
    gramDualTerm a b W Z 0 = 0 := by
  have hz := mixedFrequencyGauss_zero ha hb hsa hsb hab hne
  rw [mixedFrequencyGauss_squarefree ha hb hsa hsb hab] at hz
  have hg : gauss a * star (gauss b) ≠ 0 := by
    intro h
    have hn := norm_gramGauss_scalar ha hb hsa hsb
    rw [h, norm_zero] at hn
    norm_num at hn
  have hχ := (mul_eq_zero.mp hz).resolve_left hg
  simp only [gramDualTerm, hχ, zero_mul]

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ideal Moebius weights and exact prime-factor subset identities. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma idealMoebius_mul {a b : Eisenstein} (h : IsCoprime a b) :
    idealMoebius (a*b) = idealMoebius a * idealMoebius b :=
  (isRelPrime_iff_isCoprime.mpr h).moebius_mul

lemma idealMoebius_primaryPrime {p : Eisenstein} (hp : primaryPrime p) :
    idealMoebius p = -1 := hp.2.irreducible.moebius_eq

lemma idealMoebius_prod_primaryPrimes (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) :
    idealMoebius (∏ p ∈ s, p) = (-1 : ℤ)^s.card := by
  induction s using Finset.induction_on with
  | empty => simp [idealMoebius]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hc : IsCoprime p (∏ q ∈ s, q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun h => hps (h ▸ hq))
    rw [Finset.prod_insert hps, idealMoebius_mul hc, idealMoebius_primaryPrime hp',
      ih hs, Finset.card_insert_of_notMem hps, pow_succ]
    ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moebius removal of common factors and coprime Gram decomposition. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma summable_gram_restricted {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) (S : Eisenstein → Prop) :
    Summable (fun n : Eisenstein => if primary n ∧ S n then
      W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n) else 0) := by
  apply Summable.of_norm_bounded
    (schwartz_summable_eisenstein (normProfileSchwartz W hW hW' Z hZ)).norm
  intro n
  change ‖ite _ _ _‖ ≤ ‖W (norm n / Z)‖
  split_ifs with hn
  · rw [norm_mul, norm_mul, norm_star]
    calc
      _ ≤ ‖W (norm n / Z)‖ * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_cubicSymbol_le_one ha n)
          (_root_.norm_nonneg _)) (norm_cubicSymbol_le_one hb n)
            (_root_.norm_nonneg _) (by positivity)
      _ = _ := by ring
  · simp

end CubicFirstMoment

namespace CubicFirstMoment

theorem primarySquarefree_common_decomposition {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q) :
    ∃ k a b : Eisenstein, primary k ∧ primary a ∧ primary b ∧
      Squarefree k ∧ Squarefree a ∧ Squarefree b ∧
      IsCoprime a b ∧ IsCoprime k a ∧ IsCoprime k b ∧ p = k*a ∧ q = k*b := by
  let P := primaryPrimeFactors p
  let Q := primaryPrimeFactors q
  let k := ∏ r ∈ P ∩ Q, r
  let a := ∏ r ∈ P \ Q, r
  let b := ∏ r ∈ Q \ P, r
  have hk : primary k := primary_finset_prod _ _
    (fun r hr => (primaryPrimeFactor_spec hp (Finset.mem_inter.mp hr).1).1.1)
  have ha : primary a := primary_finset_prod _ _
    (fun r hr => (primaryPrimeFactor_spec hp (Finset.mem_sdiff.mp hr).1).1.1)
  have hb : primary b := primary_finset_prod _ _
    (fun r hr => (primaryPrimeFactor_spec hq (Finset.mem_sdiff.mp hr).1).1.1)
  have hep : k*a = p :=
    (Finset.prod_inter_mul_prod_sdiff P Q (fun r : Eisenstein => r)).trans
      (primaryPrimeFactors_prod hp hsp)
  have heq : k*b = q := by
    change (∏ r ∈ P ∩ Q, r) * (∏ r ∈ Q \ P, r) = q
    rw [Finset.inter_comm P Q]
    exact (Finset.prod_inter_mul_prod_sdiff Q P (fun r : Eisenstein => r)).trans
      (primaryPrimeFactors_prod hq hsq)
  have hab : IsCoprime a b := by
    apply IsCoprime.prod_left
    intro r hr
    apply IsCoprime.prod_right
    intro s hs
    apply primaryPrimes_isCoprime (primaryPrimeFactor_spec hp (Finset.mem_sdiff.mp hr).1).1
      (primaryPrimeFactor_spec hq (Finset.mem_sdiff.mp hs).1).1
    intro he
    exact (Finset.mem_sdiff.mp hr).2 (he ▸ (Finset.mem_sdiff.mp hs).1)
  have hka : IsCoprime k a := by
    apply IsCoprime.prod_left
    intro r hr
    apply IsCoprime.prod_right
    intro s hs
    apply primaryPrimes_isCoprime (primaryPrimeFactor_spec hp (Finset.mem_inter.mp hr).1).1
      (primaryPrimeFactor_spec hp (Finset.mem_sdiff.mp hs).1).1
    intro he
    exact (Finset.mem_sdiff.mp hs).2 (he ▸ (Finset.mem_inter.mp hr).2)
  have hkb : IsCoprime k b := by
    apply IsCoprime.prod_left
    intro r hr
    apply IsCoprime.prod_right
    intro s hs
    apply primaryPrimes_isCoprime (primaryPrimeFactor_spec hp (Finset.mem_inter.mp hr).1).1
      (primaryPrimeFactor_spec hq (Finset.mem_sdiff.mp hs).1).1
    intro he
    exact (Finset.mem_sdiff.mp hs).2 (he ▸ (Finset.mem_inter.mp hr).1)
  exact ⟨k, a, b, hk, ha, hb,
    Squarefree.squarefree_of_dvd (hep ▸ dvd_mul_right k a) hsp, Squarefree.squarefree_of_dvd (hep ▸ dvd_mul_left a k) hsp,
    Squarefree.squarefree_of_dvd (heq ▸ dvd_mul_left b k) hsq, hab, hka, hkb, hep.symm, heq.symm⟩

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_finset_prod {α : Type*} (s : Finset α) (f : α → Eisenstein) :
    norm (∏ p ∈ s, f p) = ∏ p ∈ s, norm (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih => simp [hp, ih]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic sieve operators, bilinear norms and coprime completion. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primarySmoothedSieveMass_gram (S : Finset Eisenstein)
    (hS : ∀ n ∈ S, primary n) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {M : ℝ} (hM : 0 < M) :
    primarySmoothedSieveMass S u W M =
      ∑ a ∈ S, ∑ b ∈ S, u a * star (u b) * primaryCharacterGram a b W M := by
  let F (a b x : Eisenstein) : ℂ := u a * star (u b) *
    (if primary x then W (norm x / M) * cubicSymbol a x * star (cubicSymbol b x) else 0)
  have hF (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) (hb : b ∈ S) :
      Summable (F a b) := by
    apply Summable.mul_left
    simpa only [and_true] using
      summable_gram_restricted (hS a ha) (hS b hb) W hW hW' hM (fun _ => True)
  have hpoint (x : Eisenstein) :
      (if primary x then W (norm x / M) *
        (‖∑ n ∈ S, u n * cubicSymbol n x‖^2 : ℝ) else 0) =
      ∑ a ∈ S, ∑ b ∈ S, F a b x := by
    by_cases hx : primary x
    · simp only [ite_eq_left hx, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
        map_sum, map_mul, F]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp only [starRingEnd_apply]
      ring
    · simp [hx, F]
  unfold primarySmoothedSieveMass
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hF a ha b hb))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Summable.tsum_finsetSum (hF a ha)]
  apply Finset.sum_congr rfl
  intro b hb
  exact tsum_mul_left

end CubicFirstMoment

open UniqueFactorizationMonoid
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact common-factor row reindexing and matrix decomposition. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_residualRows {S : Finset Eisenstein} {k a : Eisenstein} (hk : k ≠ 0) :
    a ∈ residualRows S k ↔ k*a ∈ S := by
  simp [residualRows,hk]

lemma residualRows_primary {S : Finset Eisenstein} {k : Eisenstein} (hk : primary k)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) :
    ∀ a ∈ residualRows S k, primary a ∧ Squarefree a := by
  intro a ha
  have hn := hS (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
  exact ⟨primary_of_mul hk hn.1,hn.2.of_mul_right⟩

lemma primaryPrimeFactors_coprime_overlap {k a b : Eisenstein}
    (hk : primary k) (ha : primary a) (hb : primary b) (hab : IsCoprime a b) :
    primaryPrimeFactors (k*a) ∩ primaryPrimeFactors (k*b) = primaryPrimeFactors k := by
  ext p
  rw [Finset.mem_inter, primaryPrime_mem_factors_iff (primary_mul hk ha),
    primaryPrime_mem_factors_iff (primary_mul hk hb), primaryPrime_mem_factors_iff hk]
  constructor
  · rintro ⟨⟨hp,hpa⟩,⟨_,hpb⟩⟩
    refine ⟨hp,?_⟩
    rcases hp.2.dvd_mul.mp hpa with hd | hd
    · exact hd
    rcases hp.2.dvd_mul.mp hpb with hd' | hd'
    · exact hd'
    exact (hp.2.not_isUnit (hab.isUnit_of_dvd' hd hd')).elim
  · rintro ⟨hp,hd⟩
    exact ⟨⟨hp,hd.trans (dvd_mul_right k a)⟩,⟨hp,hd.trans (dvd_mul_right k b)⟩⟩

lemma primaryCommonFactor_mul {k a b : Eisenstein}
    (hk : primary k) (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) : primaryCommonFactor (k*a) (k*b) = k := by
  unfold primaryCommonFactor
  rw [primaryPrimeFactors_coprime_overlap hk ha hb hab,primaryPrimeFactors_prod hk hsk]

lemma primaryCommonFactor_spec {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q) :
    primary (primaryCommonFactor p q) ∧ Squarefree (primaryCommonFactor p q) ∧
      primaryCommonFactor p q ∣ p ∧ primaryCommonFactor p q ∣ q := by
  obtain ⟨k,a,b,hk,ha,hb,hsk,hsa,hsb,hab,_,_,hpa,hqb⟩ :=
    primarySquarefree_common_decomposition hp hq hsp hsq
  have he : primaryCommonFactor p q = k := hpa ▸ hqb ▸ primaryCommonFactor_mul hk hsk ha hb hab
  rw [he,hpa,hqb]
  exact ⟨hk,hsk,dvd_mul_right k a,dvd_mul_right k b⟩

lemma commonRowFactors_spec {S : Finset Eisenstein}
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) {k : Eisenstein}
    (hk : k ∈ commonRowFactors S) : primary k ∧ Squarefree k := by
  obtain ⟨⟨p,q⟩,hpq,rfl⟩ := Finset.mem_image.mp hk
  have hp := hS p (Finset.mem_product.mp hpq).1
  have hq := hS q (Finset.mem_product.mp hpq).2
  exact ⟨(primaryCommonFactor_spec hp.1 hq.1 hp.2 hq.2).1,
    (primaryCommonFactor_spec hp.1 hq.1 hp.2 hq.2).2.1⟩

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CellBounds
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two-variable localization bounds

The finite inequalities underlying `eq:near-cell-diagonal`,
`eq:all-cell-error`, and `eq:far-cell-diagonal` in the sharp-cutoff argument.
The incidence set records which pairs of norm cells meet the product boundary.
Both row and column degrees enter the near-boundary bound.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

/-- Counting a cell's energy once for each of its incident pairs costs at
most the degree bound. -/
theorem cell_incidence_energy {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (E : Finset (ι × κ)) (a : ι → ℝ) (D : ℕ)
    (hI : ∀ e ∈ E, e.1 ∈ I)
    (hD : ∀ i ∈ I, (E.filter (fun e => e.1 = i)).card ≤ D) :
    (∑ e ∈ E, (a e.1) ^ 2) ≤ (D : ℝ) * ∑ i ∈ I, (a i) ^ 2 := by
  rw [← Finset.sum_fiberwise_of_maps_to hI (fun e => (a e.1) ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    (∑ e ∈ E.filter (fun e => e.1 = i), (a e.1) ^ 2) =
        ((E.filter (fun e => e.1 = i)).card : ℝ) * (a i) ^ 2 := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hD i hi) (sq_nonneg _)

/-- The corresponding column-energy bound. -/
theorem cell_incidence_energy_right {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (J : Finset κ) (E : Finset (ι × κ)) (b : κ → ℝ) (D : ℕ)
    (hJ : ∀ e ∈ E, e.2 ∈ J)
    (hD : ∀ j ∈ J, (E.filter (fun e => e.2 = j)).card ≤ D) :
    (∑ e ∈ E, (b e.2) ^ 2) ≤ (D : ℝ) * ∑ j ∈ J, (b j) ^ 2 := by
  rw [← Finset.sum_fiberwise_of_maps_to hJ (fun e => (b e.2) ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  calc
    (∑ e ∈ E.filter (fun e => e.2 = j), (b e.2) ^ 2) =
        ((E.filter (fun e => e.2 = j)).card : ℝ) * (b j) ^ 2 := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hD j hj) (sq_nonneg _)

/-- Localizing both variables gives the bounded-degree Cauchy inequality.
Only the near pairs are summed, rather than all pairs of cells. -/
theorem near_cell_sum_sq {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (E : Finset (ι × κ))
    (a : ι → ℝ) (b : κ → ℝ) (D : ℕ)
    (hI : ∀ e ∈ E, e.1 ∈ I) (hJ : ∀ e ∈ E, e.2 ∈ J)
    (hrow : ∀ i ∈ I, (E.filter (fun e => e.1 = i)).card ≤ D)
    (hcol : ∀ j ∈ J, (E.filter (fun e => e.2 = j)).card ≤ D) :
    (∑ e ∈ E, a e.1 * b e.2) ^ 2 ≤
      (D : ℝ) ^ 2 * (∑ i ∈ I, (a i) ^ 2) * ∑ j ∈ J, (b j) ^ 2 := by
  have ha := cell_incidence_energy I E a D hI hrow
  have hb := cell_incidence_energy_right J E b D hJ hcol
  calc
    _ ≤ (∑ e ∈ E, (a e.1) ^ 2) * ∑ e ∈ E, (b e.2) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq E _ _
    _ ≤ ((D : ℝ) * ∑ i ∈ I, (a i) ^ 2) *
        ((D : ℝ) * ∑ j ∈ J, (b j) ^ 2) :=
      mul_le_mul ha hb (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by ring

/-- Unsquaring the near-boundary estimate. The cell masses are L² norms
in the application and are thus nonnegative. -/
theorem near_cell_sum_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (E : Finset (ι × κ))
    (a : ι → ℝ) (b : κ → ℝ) (D : ℕ)
    (hI : ∀ e ∈ E, e.1 ∈ I) (hJ : ∀ e ∈ E, e.2 ∈ J)
    (hrow : ∀ i ∈ I, (E.filter (fun e => e.1 = i)).card ≤ D)
    (hcol : ∀ j ∈ J, (E.filter (fun e => e.2 = j)).card ≤ D) :
    (∑ e ∈ E, a e.1 * b e.2) ≤
      (D : ℝ) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) *
        Real.sqrt (∑ j ∈ J, (b j) ^ 2) := by
  have h := near_cell_sum_sq I J E a b D hI hJ hrow hcol
  have ha := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ I) => sq_nonneg (a i)))
  have hb := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ J) => sq_nonneg (b j)))
  have he : ((D : ℝ) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) *
      Real.sqrt (∑ j ∈ J, (b j) ^ 2)) ^ 2 =
      (D : ℝ) ^ 2 * (∑ i ∈ I, (a i) ^ 2) * ∑ j ∈ J, (b j) ^ 2 := by
    rw [mul_pow, mul_pow, ha, hb]
  rw [← he] at h
  have hn : 0 ≤ (D : ℝ) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) *
      Real.sqrt (∑ j ∈ J, (b j) ^ 2) := by positivity
  nlinarith

/-- Without a near-pair restriction, the sum of cell masses costs the
square root of the number of cells on each side. -/
theorem cell_mass_sum_sq {ι : Type*} (I : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ I, a i) ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, (a i) ^ 2 := by
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
    Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) a

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CellGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the product-boundary cells

After scaling log-norm by the cell width, the two norm cells are unit
intervals. A pair meeting a width-one strip around the product boundary
can lie on only five integer diagonals. This proves the bounded-neighbor
claim used in `eq:near-cell-diagonal` rather than postulating it.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

/-- A cell pair that meets the boundary strip has one of five index sums. -/
theorem nearCell_index_mem {i j : ℤ} {x y c : ℝ}
    (hx : (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1)
    (hy : (j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1)
    (hnear : |x + y - c| ≤ 1) : i + j ∈ nearCellOffsets c := by
  rcases abs_le.mp hnear with ⟨hl, hu⟩
  have hf := Int.floor_le c
  have hf' := Int.lt_floor_add_one c
  have hlo : ((⌊c⌋ - 3 : ℤ) : ℝ) ≤ ((i + j : ℤ) : ℝ) := by
    push_cast
    linarith
  have hhi : ((i + j : ℤ) : ℝ) < ((⌊c⌋ + 2 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hhi' : i + j < ⌊c⌋ + 2 := by exact_mod_cast hhi
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo, by omega⟩

theorem nearCell_row_degree (E : Finset (ℤ × ℤ)) (c : ℝ)
    (hE : ∀ e ∈ E, e.1 + e.2 ∈ nearCellOffsets c) (i : ℤ) :
    (E.filter (fun e => e.1 = i)).card ≤ 5 := by
  rw [← nearCellOffsets_card c]
  apply Finset.card_le_card_of_injOn (fun e : ℤ × ℤ => e.1 + e.2)
  · intro e he
    exact hE e (Finset.mem_filter.mp he).1
  · intro e he f hf hsum
    have he' := (Finset.mem_filter.mp he).2
    have hf' := (Finset.mem_filter.mp hf).2
    change e.1 + e.2 = f.1 + f.2 at hsum
    apply Prod.ext
    · exact he'.trans hf'.symm
    · omega

theorem nearCell_column_degree (E : Finset (ℤ × ℤ)) (c : ℝ)
    (hE : ∀ e ∈ E, e.1 + e.2 ∈ nearCellOffsets c) (j : ℤ) :
    (E.filter (fun e => e.2 = j)).card ≤ 5 := by
  rw [← nearCellOffsets_card c]
  apply Finset.card_le_card_of_injOn (fun e : ℤ × ℤ => e.1 + e.2)
  · intro e he
    exact hE e (Finset.mem_filter.mp he).1
  · intro e he f hf hsum
    have he' := (Finset.mem_filter.mp he).2
    have hf' := (Finset.mem_filter.mp hf).2
    change e.1 + e.2 = f.1 + f.2 at hsum
    apply Prod.ext
    · omega
    · exact he'.trans hf'.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact corrected-dispersion identities

The polynomials below are those in `eq:dispersion-polynomials` of the
manuscript. The factorization is valid even with a common prime factor:
the already proved Gauss-sum multiplication law then makes the summand zero.
The norm estimates here do not assume the new dispersion bounds.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

theorem normTwist_mul (u : ℝ) {a b : Eisenstein}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    normTwist u (a * b) = normTwist u a * normTwist u b := by
  have han : norm a ≠ 0 := (norm_eq_zero_iff.not.mpr ha)
  have hbn : norm b ≠ 0 := (norm_eq_zero_iff.not.mpr hb)
  have hn : norm (a * b) = norm a * norm b := Complex.normSq_mul _ _
  simp only [normTwist, hn, Real.log_mul han hbn, mul_add, Complex.ofReal_add,
    add_mul, Complex.exp_add]

theorem norm_gauss_le_one {a : Eisenstein} (ha : primary a) : ‖gauss a‖ ≤ 1 := by
  rw [norm_gauss ha]
  split_ifs <;> norm_num

/-- Exact factorization of the bilinear Gauss sum into the dispersion rows. -/
theorem bilinear_gauss_eq_rows (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b) :
    (∑ a ∈ A, ∑ b ∈ B, α a * β b * gauss (a * b) * normTwist u (a * b)) =
      ∑ a ∈ A, α a * normTwist u a * gauss a * dispersionPolynomial B β u a := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [dispersionPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [gauss_mul (hA a ha) (hB b hb),
    normTwist_mul u (primary_ne_zero (hA a ha)) (primary_ne_zero (hB b hb))]
  ring

/-- Finite Cauchy--Schwarz for the actual complex row sum. -/
theorem complex_bilinear_rows_sq {ι : Type*} (A : Finset ι) (α F : ι → ℂ) :
    ‖∑ a ∈ A, α a * F a‖ ^ 2 ≤
      (∑ a ∈ A, ‖α a‖ ^ 2) * ∑ a ∈ A, ‖F a‖ ^ 2 := by
  calc
    _ ≤ (∑ a ∈ A, ‖α a * F a‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (norm_sum_le _ _) 2
    _ = (∑ a ∈ A, ‖α a‖ * ‖F a‖) ^ 2 := by simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq A _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredHeightMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite frequency blocks retain the proved height mean, with an explicit
row count for the actual ramified and cube decomposition. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_dyadic_integral_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ a ∈ S, Continuous (f a)) (T : ℝ) :
    ((∫ t in T..2*T, ∑ a ∈ S, f a t) + (∫ t in -2*T..-T, ∑ a ∈ S, f a t))/T =
      ∑ a ∈ S, ((∫ t in T..2*T, f a t)+(∫ t in -2*T..-T, f a t))/T := by
  rw [intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    ← Finset.sum_add_distrib,Finset.sum_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightAveraging
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive, normalized two-sided height averaging. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadicHeightMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ g t) :
    dyadicHeightMean f T ≤ dyadicHeightMean g T := by
  apply div_le_div_of_nonneg_right _ hT.le
  apply add_le_add
  · apply intervalIntegral.integral_mono_on (by linarith : T ≤ 2*T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨by linarith [ht.1],ht.2⟩
  · apply intervalIntegral.integral_mono_on (by linarith : -2*T ≤ -T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨ht.1,by linarith [ht.2]⟩

lemma dyadicHeightMean_const (C : ℝ) {T : ℝ} (hT : T ≠ 0) :
    dyadicHeightMean (fun _ => C) T = 2*C := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const,smul_eq_mul]
  field_simp
  ring

lemma dyadicHeightMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (T : ℝ) :
    dyadicHeightMean (fun t => f t+g t) T = dyadicHeightMean f T+dyadicHeightMean g T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_add
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

lemma dyadicHeightMean_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ a ∈ S, Continuous (f a)) (T : ℝ) :
    dyadicHeightMean (fun t => ∑ a ∈ S, f a t) T = ∑ a ∈ S, dyadicHeightMean (f a) T :=
  finite_dyadic_integral_sum S f hf T

lemma dyadicHeightMean_const_mul (c : ℝ) (f : ℝ → ℝ) (T : ℝ) :
    dyadicHeightMean (fun t => c*f t) T = c*dyadicHeightMean f T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicWeightIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported height weight is controlled by the actual two-sided
dyadic mean. The normalization includes both height intervals. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma dyadicWeightIntegral_bound (f h : ℝ → ℂ) (hf : Continuous f)
    {T M : ℝ} (hT : 0 < T) (_hM : 0 ≤ M) (hh : ∀ t, ‖h t‖ ≤ M)
    (hs : ∀ t, t ∉ dyadicHeightSupport T → h t = 0) :
    ‖∫ t : ℝ, h t*f t‖ ≤ M*T*dyadicHeightMean (fun t => ‖f t‖) T := by
  let g := fun t : ℝ => M*‖f t‖
  have hg : Continuous g := continuous_const.mul hf.norm
  have hU : MeasurableSet (dyadicHeightSupport T) := measurableSet_Icc.union measurableSet_Icc
  have hgi : Integrable ((dyadicHeightSupport T).indicator g) :=
    (hg.continuousOn.integrableOn_compact (isCompact_Icc.union isCompact_Icc)).integrable_indicator hU
  have hb : ‖∫ t : ℝ, h t*f t‖ ≤ ∫ t : ℝ, (dyadicHeightSupport T).indicator g t := by
    apply norm_integral_le_of_norm_le hgi
    filter_upwards with t
    by_cases ht : t ∈ dyadicHeightSupport T
    · rw [indicator_of_mem ht,norm_mul]
      exact mul_le_mul_of_nonneg_right (hh t) (_root_.norm_nonneg _)
    · rw [indicator_of_notMem ht,hs t ht,zero_mul,norm_zero]
  have hd : Disjoint (Icc T (2*T)) (Icc (-2*T) (-T)) := by
    apply Set.disjoint_left.mpr
    intro t hp hn
    linarith [hp.1,hn.2]
  rw [integral_indicator hU] at hb
  change ‖∫ t : ℝ, h t*f t‖ ≤ ∫ t in Icc T (2*T) ∪ Icc (-2*T) (-T), g t at hb
  rw [setIntegral_union hd measurableSet_Icc hg.integrableOn_Icc hg.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : T ≤ 2*T),
    ←intervalIntegral.integral_of_le (by linarith : -2*T ≤ -T)] at hb
  apply hb.trans_eq
  dsimp [g,dyadicHeightMean]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  field_simp

lemma normalized_dyadicWeightIntegral_bound (f h : ℝ → ℂ) (hf : Continuous f)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hh : ∀ t, ‖h t‖ ≤ M)
    (hs : ∀ t, t ∉ dyadicHeightSupport T → h t = 0) :
    ‖(T:ℂ)⁻¹*(∫ t : ℝ, h t*f t)‖ ≤ M*dyadicHeightMean (fun t => ‖f t‖) T := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hT.le]
  have hb := mul_le_mul_of_nonneg_left (dyadicWeightIntegral_bound f h hf hT hM hh hs)
    (inv_nonneg.mpr hT.le)
  apply hb.trans_eq
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightIntegrationByParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact twofold integration by parts for the actual height exponential. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace CubicFirstMoment

lemma heightFourierIntegral_eq (h : ℝ → ℂ) (ℓ : ℝ) :
    heightFourierIntegral h ℓ = ∫ t : ℝ, h t*Complex.exp ((ℓ*t:ℝ)*Complex.I) := by
  rw [heightFourierIntegral,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  have he : -2*Real.pi*t*(-ℓ/(2*Real.pi)) = ℓ*t := by
    field_simp
  rw [he,smul_eq_mul,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightMeanSquare
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite spectral expansion of the height-averaged square.
The diagonal and every off-diagonal pair are retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_normTwist (b : Eisenstein) : Continuous (fun u : ℝ => normTwist u b) := by
  unfold normTwist
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Fourier decay for the fixed wider log-norm cutoff used by the
actual prime convolution. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma wideGramExp_deriv_bound (M : ℝ) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (i : ℕ), i ≤ n → ∀ u : ℝ, |u| ≤ 2*M →
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ u ∈ Set.Icc (-2*M) (2*M),
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D :=
    isCompact_Icc.exists_bound_of_continuousOn
      (gramExp_contDiff.continuous_iteratedFDeriv (mod_cast le_top)).continuousOn
  choose B hB using hb
  let D := 1 + ∑ i ∈ Finset.range (n+1), |B i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n+1), |B i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro i hi u hu
  have hbi : |B i| ≤ ∑ j ∈ Finset.range (n+1), |B j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_range.mpr (by omega))
  exact (hB i u ⟨by linarith [(abs_le.mp hu).1], (abs_le.mp hu).2⟩).trans
    ((le_abs_self (B i)).trans (hbi.trans (by dsimp [D]; linarith)))

lemma wideGramExp_scale_growth {M c u : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hu : |u| ≤ 2*M) :
    1+c ≤ Real.exp M * (1+‖c • gramExp u‖) := by
  have hE : 1 ≤ Real.exp M := Real.one_le_exp hM
  have hEu : 1 ≤ Real.exp M * Real.exp (u/2) := by
    rw [← Real.exp_add]
    simpa using Real.exp_le_exp.mpr (show (0:ℝ) ≤ M + u/2 by
      linarith [(abs_le.mp hu).1])
  have hEc := mul_le_mul_of_nonneg_left hEu hc
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, gramExp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith

lemma wideAnnularLogSchwartz_deriv_zero (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (c u : ℝ) (n : ℕ)
    (hu : ¬ |u| ≤ 2*M) : iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u = 0 := by
  by_contra hn
  have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := wideAnnularLogSchwartz M hM F c) n hn
  have hb := tsupport_smul_subset_left ((wideGramLogBump M hM) : ℝ → ℝ)
    (fun v => F (c • gramExp v)) hs
  rw [(wideGramLogBump M hM).tsupport_eq] at hb
  exact hu (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, wideGramLogBump] using hb)

lemma wideAnnularLogSchwartz_eq_wideGramLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ) =
      wideGramLogSchwartz M hM W hW hW' ρ := by
  ext u
  simp only [wideAnnularLogSchwartz_apply M hM, wideGramLogSchwartz_apply, wideGramLogKernel,
    normProfileFourierSchwartz_apply]
  congr 2
  simp only [gramExp, Complex.real_smul, Complex.ofReal_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormDenominatorMellin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm denominator in the actual Poisson formula stays in its
Mellin kernel. No real power is inserted into the prime coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment


lemma normDenominatorLogSchwartz_eq_annular (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ =
      SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ)) := by
  rw [wideAnnularLogSchwartz_eq_wideGramLogSchwartz]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FarHeightBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform height means pass through the far-cutoff Mellin integral.
All frequency shifts are retained and the constant is independent of J. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

lemma norm_indexed_norm_polynomial {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (n : ι → Eisenstein) (t : ℝ) :
    ‖∑ a ∈ S, c a*normTwist t (n a)‖ ≤ ∑ a ∈ S, ‖c a‖ := by
  simpa only [norm_mul,norm_normTwist,mul_one] using
    norm_sum_le S (fun a => c a*normTwist t (n a))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightPolynomialIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact interchange between finite height Fourier coefficients and the
actual norm polynomial. No frequency truncation is used. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma height_norm_phase (a : Eisenstein) (x₀ t : ℝ) :
    Complex.exp (((Real.log (norm a)-x₀)*t:ℝ)*Complex.I) =
      Complex.exp ((-x₀*t:ℝ)*Complex.I)*normTwist t a := by
  unfold normTwist
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integrable_height_phase (h : ℝ → ℂ) (hi : Integrable h) (ℓ : ℝ) :
    Integrable (fun t : ℝ => h t*Complex.exp ((ℓ*t:ℝ)*Complex.I)) := by
  apply hi.mul_bdd (c := 1)
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp ((ℓ*t:ℝ)*Complex.I))).aestronglyMeasurable
  · exact Eventually.of_forall (fun _ => by simp [Complex.norm_exp])

theorem height_norm_polynomial_integral {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (n : ι → Eisenstein) (h : ℝ → ℂ) (hi : Integrable h) (x₀ : ℝ) :
    (∑ a ∈ S, c a*heightFourierIntegral h (Real.log (norm (n a))-x₀)) =
      ∫ t : ℝ, (h t*Complex.exp ((-x₀*t:ℝ)*Complex.I))*
        ∑ a ∈ S, c a*normTwist t (n a) := by
  calc
    _ = ∑ a ∈ S, ∫ t : ℝ, c a*(h t*
        Complex.exp (((Real.log (norm (n a))-x₀)*t:ℝ)*Complex.I)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [heightFourierIntegral_eq,integral_const_mul]
    _ = ∫ t : ℝ, ∑ a ∈ S, c a*(h t*
        Complex.exp (((Real.log (norm (n a))-x₀)*t:ℝ)*Complex.I)) :=
      (integral_finsetSum S (fun a _ =>
        (integrable_height_phase h hi (Real.log (norm (n a))-x₀)).const_mul (c a))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [height_norm_phase]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogNormCells
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual disjoint log-norm partition used in the integrated bilinear
estimate. Its finite fibers preserve both the sum and coefficient energy. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma logNormCell_bounds (J A : ℝ) (a : Eisenstein) :
    (logNormCell J A a : ℝ) ≤ J*Real.log (norm a/A) ∧
    J*Real.log (norm a/A) < (logNormCell J A a : ℝ)+1 :=
  ⟨Int.floor_le _,Int.lt_floor_add_one _⟩

lemma logNormCell_mem_range {S : Finset Eisenstein} {J A R : ℝ}
    (hS : ∀ a ∈ S, 0 ≤ J*Real.log (norm a/A) ∧ J*Real.log (norm a/A) ≤ R)
    {a : Eisenstein} (ha : a ∈ S) :
    logNormCell J A a ∈ Finset.Icc 0 ⌊R⌋ := by
  apply Finset.mem_Icc.mpr
  exact ⟨Int.floor_nonneg.mpr (hS a ha).1,Int.floor_mono (hS a ha).2⟩

lemma logNormCell_count {S : Finset Eisenstein} {J A R : ℝ}
    (hS : ∀ a ∈ S, 0 ≤ J*Real.log (norm a/A) ∧ J*Real.log (norm a/A) ≤ R) :
    (S.image (logNormCell J A)).card ≤ (⌊R⌋+1).toNat := by
  have h := Finset.card_le_card (show S.image (logNormCell J A) ⊆ Finset.Icc 0 ⌊R⌋ by
    intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    exact logNormCell_mem_range hS ha)
  simpa only [Int.card_Icc,sub_zero] using h

lemma sum_logNormCells {M : Type*} [AddCommMonoid M]
    (S : Finset Eisenstein) (J A : ℝ) (f : Eisenstein → M) :
    (∑ i ∈ S.image (logNormCell J A), ∑ a ∈ logNormCellSupport S J A i, f a) =
      ∑ a ∈ S, f a := by
  exact Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) f

lemma logNormCell_energy (S : Finset Eisenstein) (J A : ℝ) (α : Eisenstein → ℂ) :
    (∑ i ∈ S.image (logNormCell J A),
      (Real.sqrt (∑ a ∈ logNormCellSupport S J A i, ‖α a‖^2))^2) =
      ∑ a ∈ S, ‖α a‖^2 := by
  simp_rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact sum_logNormCells S J A (fun a => ‖α a‖^2)

lemma logNormCell_bilinear_partition (P S : Finset Eisenstein)
    (J A B : ℝ) (f : Eisenstein → Eisenstein → ℂ) :
    (∑ a ∈ P, ∑ b ∈ S, f a b) =
      ∑ i ∈ P.image (logNormCell J A), ∑ j ∈ S.image (logNormCell J B),
        ∑ a ∈ logNormCellSupport P J A i, ∑ b ∈ logNormCellSupport S J B j, f a b := by
  rw [←sum_logNormCells P J A (fun a => ∑ b ∈ S, f a b)]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ a ∈ logNormCellSupport P J A i,
        ∑ j ∈ S.image (logNormCell J B), ∑ b ∈ logNormCellSupport S J B j, f a b := by
      exact Finset.sum_congr rfl (fun a _ => (sum_logNormCells S J B (f a)).symm)
    _ = _ := Finset.sum_comm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NearLogNormCells
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual log-norm cells meeting the product boundary have degree at
most five. The near-cell diagonal therefore retains the inverse cell width. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma scaled_log_product (a b : Eisenstein) (ha : a ≠ 0) (hb : b ≠ 0)
    (J : ℝ) {A B X₀ : ℝ} (hA : 0 < A) (hB : 0 < B) (hX : 0 < X₀) :
    J*Real.log (norm a/A)+J*Real.log (norm b/B)-J*Real.log (X₀/(A*B)) =
      J*Real.log (norm (a*b)/X₀) := by
  have han : norm a ≠ 0 := norm_eq_zero_iff.not.mpr ha
  have hbn : norm b ≠ 0 := norm_eq_zero_iff.not.mpr hb
  rw [show norm (a*b) = norm a*norm b from Complex.normSq_mul _ _,
    Real.log_div han hA.ne',Real.log_div hbn hB.ne',
    Real.log_div hX.ne' (mul_ne_zero hA.ne' hB.ne'),
    Real.log_div (mul_ne_zero han hbn) hX.ne',
    Real.log_mul han hbn,Real.log_mul hA.ne' hB.ne']
  ring

lemma nearLogNormCells_offsets (P S : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (J : ℝ) {A B X₀ : ℝ} (hA : 0 < A) (hB : 0 < B) (hX : 0 < X₀) :
    ∀ e ∈ nearLogNormCells P S J A B X₀,
      e.1+e.2 ∈ nearCellOffsets (J*Real.log (X₀/(A*B))) := by
  intro e he
  obtain ⟨a,ha,b,hb,hai,hbj,hn⟩ := (Finset.mem_filter.mp he).2
  have hx := logNormCell_bounds J A a
  have hy := logNormCell_bounds J B b
  rw [hai] at hx
  rw [hbj] at hy
  rw [←scaled_log_product a b (primary_ne_zero (hP a ha))
    (primary_ne_zero (hS b hb)) J hA hB hX] at hn
  exact nearCell_index_mem ⟨hx.1,hx.2.le⟩ ⟨hy.1,hy.2.le⟩ hn

theorem nearLogNormCells_energy_bound (P S : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (α β : Eisenstein → ℂ) (J : ℝ) {A B X₀ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hX : 0 < X₀) :
    (∑ e ∈ nearLogNormCells P S J A B X₀,
      Real.sqrt (∑ a ∈ logNormCellSupport P J A e.1, ‖α a‖^2)*
      Real.sqrt (∑ b ∈ logNormCellSupport S J B e.2, ‖β b‖^2)) ≤
      5*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  classical
  let E := nearLogNormCells P S J A B X₀
  have he := nearLogNormCells_offsets P S hP hS J hA hB hX
  have hrow (i : ℤ) : (E.filter (fun e => e.1 = i)).card ≤ 5 :=
    nearCell_row_degree E _ he i
  have hcol (j : ℤ) : (E.filter (fun e => e.2 = j)).card ≤ 5 :=
    nearCell_column_degree E _ he j
  have hm := near_cell_sum_le (P.image (logNormCell J A)) (S.image (logNormCell J B)) E
    (fun i => Real.sqrt (∑ a ∈ logNormCellSupport P J A i, ‖α a‖^2))
    (fun j => Real.sqrt (∑ b ∈ logNormCellSupport S J B j, ‖β b‖^2)) 5
    (fun e he => (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1)
    (fun e he => (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2)
    (fun i _ => hrow i) (fun j _ => hcol j)
  simpa only [logNormCell_energy,Nat.cast_ofNat] using hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FarLogNormCells
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Far cells are the exact complement of the actual near-cell graph.
Every product in such a cell has the lower frequency bound needed for IBP. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma nearLogNormCells_subset (P S : Finset Eisenstein) (J A B X₀ : ℝ) :
    nearLogNormCells P S J A B X₀ ⊆ allLogNormCells P S J A B :=
  Finset.filter_subset _ _

lemma sum_near_farLogNormCells {M : Type*} [AddCommMonoid M]
    (P S : Finset Eisenstein) (J A B X₀ : ℝ) (f : ℤ × ℤ → M) :
    (∑ e ∈ nearLogNormCells P S J A B X₀, f e)+
      (∑ e ∈ farLogNormCells P S J A B X₀, f e) =
      ∑ e ∈ allLogNormCells P S J A B, f e := by
  rw [add_comm]
  exact Finset.sum_sdiff (nearLogNormCells_subset P S J A B X₀)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CellMassAggregation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing arbitrary cell pairs costs the square roots of their counts.
These bounds also apply to the far-cell subset. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cell_mass_sum_le {ι : Type*} (I : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ I, a i) ≤ Real.sqrt (I.card:ℝ)*Real.sqrt (∑ i ∈ I, (a i)^2) := by
  have hh := cell_mass_sum_sq I a
  have hcard : 0 ≤ (I.card:ℝ) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ i ∈ I, (a i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : (Real.sqrt (I.card:ℝ)*Real.sqrt (∑ i ∈ I, (a i)^2))^2 =
      (I.card:ℝ)*(∑ i ∈ I, (a i)^2) := by
    rw [mul_pow,Real.sq_sqrt hcard,Real.sq_sqrt hsum]
  rw [←hs] at hh
  have hn : 0 ≤ Real.sqrt (I.card:ℝ)*Real.sqrt (∑ i ∈ I, (a i)^2) := by positivity
  nlinarith only [hh,hn]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogCellCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! There are at most 2J populated cells in a dyadic norm interval.
The resulting all-pair mass bound uses the original coefficient energies. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadic_logCell_card_bound (P : Finset Eisenstein) {J A : ℝ} (hJ : 1 ≤ J)
    (hP : ∀ a ∈ P, 1 ≤ norm a/A ∧ norm a/A ≤ 2) :
    ((P.image (logNormCell J A)).card:ℝ) ≤ 2*J := by
  have hJ0 : 0 ≤ J := le_trans zero_le_one hJ
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hr : ∀ a ∈ P, 0 ≤ J*Real.log (norm a/A) ∧
      J*Real.log (norm a/A) ≤ J*Real.log 2 := by
    intro a ha
    exact ⟨mul_nonneg hJ0 (Real.log_nonneg (hP a ha).1),
      mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [(hP a ha).1]) (hP a ha).2) hJ0⟩
  have hc := logNormCell_count hr
  have hz : 0 ≤ ⌊J*Real.log 2⌋ := Int.floor_nonneg.mpr (mul_nonneg hJ0 hlog)
  have hci : ((P.image (logNormCell J A)).card:ℤ) ≤ ⌊J*Real.log 2⌋+1 := by omega
  have hcr : ((P.image (logNormCell J A)).card:ℝ) ≤ (⌊J*Real.log 2⌋:ℝ)+1 := by
    exact_mod_cast hci
  have hfl := Int.floor_le (J*Real.log 2)
  nlinarith [mul_le_mul_of_nonneg_left hlog1 hJ0]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact arithmetic identity for dispersion

The existing lattice Poisson theorem is applied to the actual Gauss-sum
rows. Conjugation reverses the mixed-character pair; the two normalized
Gauss factors then cancel. The resulting identity retains the dispersion remainder explicitly.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

theorem dispersionPolynomial_conj (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (a : Eisenstein) :
    dispersionPolynomial B β u a =
      star (∑ b ∈ B, star (dispersionAmplitude β u b) * cubicSymbol b a) := by
  simp only [dispersionPolynomial, star_sum, star_mul, star_star, dispersionAmplitude, mul_comm]

/-- The full lattice variance is precisely a finite quadratic form in
primary character Gram entries. -/
theorem smoothedDispersionVariance_gram (B : Finset Eisenstein)
    (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    smoothedDispersionVariance B β u W A =
      ∑ p ∈ B, ∑ q ∈ B, dispersionAmplitude β u p * star (dispersionAmplitude β u q) *
        primaryCharacterGram q p W A := by
  have he : smoothedDispersionVariance B β u W A =
      primarySmoothedSieveMass B (fun b => star (dispersionAmplitude β u b)) W A := by
    unfold smoothedDispersionVariance primarySmoothedSieveMass
    apply tsum_congr
    intro a
    rw [dispersionPolynomial_conj, norm_star]
  rw [he, primarySmoothedSieveMass_gram B hB _ W hW hW' hA, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  simp only [star_star]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightPoissonDyadic
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the actual height-averaged frequency annuli at their natural
Poisson scale; arbitrary subsets of each annulus are allowed. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dyadicHeightMean_norm_sum_le {α : Type*} (I : Finset α) (F : α → ℝ → ℂ)
    (hF : ∀ i ∈ I, Continuous (F i)) {T : ℝ} (hT : 0 < T) :
    dyadicHeightMean (fun t => ‖∑ i ∈ I, F i t‖) T ≤
      ∑ i ∈ I, dyadicHeightMean (fun t => ‖F i t‖) T := by
  have h := dyadicHeightMean_mono (continuous_finsetSum I hF).norm
    (continuous_finsetSum I (fun i hi => (hF i hi).norm)) hT
    (fun t _ => norm_sum_le _ _)
  exact h.trans_eq (dyadicHeightMean_sum I (fun i t => ‖F i t‖)
    (fun i hi => (hF i hi).norm) T)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SchwartzLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Poisson proof of the lattice approximation needed by the cubic profile. -/

noncomputable section
open scoped BigOperators SchwartzMap
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma traceFourier_zero (F : ℂ → ℂ) : traceFourier F 0 = ∫ z : ℂ, F z := by
  simp [traceFourier,tracePair]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SievedDispersion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact assembly of the sieved dispersion variance

The positive majorant is the finite sum of the square-divisor variances.
This makes the collected coefficients and the restricted Poisson formula
apply to the original arithmetic polynomial.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_dispersionPolynomial_le (B : Finset Eisenstein)
    (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ) (a : Eisenstein) :
    ‖dispersionPolynomial B β u a‖ ≤ ∑ b ∈ B, ‖dispersionAmplitude β u b‖ := by
  apply (norm_sum_le B _).trans
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul,norm_star]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hB b hb) a)

lemma summable_restricted_dispersion (P : Eisenstein → Prop) (B : Finset Eisenstein)
    (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    Summable (fun a : Eisenstein => if primary a ∧ P a then
      W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0) := by
  let R := ∑ b ∈ B, ‖dispersionAmplitude β u b‖
  have hs := (schwartz_summable_eisenstein (normProfileSchwartz W hW hW' A hA)).norm
  apply (hs.mul_right (R^2)).of_norm_bounded
  intro a
  change ‖ite _ _ _‖ ≤ ‖W (norm a/A)‖*R^2
  split_ifs with ha
  · rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
    exact pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_dispersionPolynomial_le B hB β u a) 2
  · rw [norm_zero]
    positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite coprimality density at a squarefree primary level.
Only residue-ring cardinalities and the ordinary Chinese remainder theorem
enter this calculation. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticTotient_mul {a b : Eisenstein} (hab : IsCoprime a b) :
    metaplecticTotient (a*b) = metaplecticTotient a*metaplecticTotient b := by
  let e : Residues (a*b) ≃+* Residues a × Residues b :=
    (Ideal.quotEquivOfEq (show modulus (a*b) = modulus a*modulus b by
      exact (Ideal.span_singleton_mul_span_singleton a b).symm)).trans
      (Ideal.quotientMulEquivQuotientProd _ _
        ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))
  have hc := Nat.card_congr ((Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits).toEquiv
  simpa only [metaplecticTotient,Nat.card_prod,Nat.cast_mul] using congrArg (fun n : ℕ => (n:ℝ)) hc

lemma metaplecticTotient_prime {p : Eisenstein} (hp : primaryPrime p) :
    metaplecticTotient p = norm p-1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have hn : 1 ≤ normNat p := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (normNat_ne_zero hp.2.ne_zero))
  rw [metaplecticTotient,Nat.card_units,residues_card hp.2.ne_zero,Nat.cast_sub hn,normNat_cast]
  norm_num

lemma metaplecticTotient_prod (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) :
    metaplecticTotient (∏ p ∈ s,p) = ∏ p ∈ s,(norm p-1) := by
  induction s using Finset.induction_on with
  | empty =>
      change (Nat.card (Residues (1:Eisenstein))ˣ:ℝ) = 1
      have hc : Nat.card (Residues (1:Eisenstein)) = 1 := by
        rw [residues_card one_ne_zero,normNat_one]
      have hsub : Subsingleton (Residues (1:Eisenstein)) :=
        (Nat.card_eq_one_iff_unique.mp hc).1
      have hunit : ∀ u : (Residues (1:Eisenstein))ˣ, u = 1 := by
        intro u
        apply Units.ext
        exact hsub.elim _ _
      have hu : Nat.card (Residues (1:Eisenstein))ˣ = 1 :=
        Nat.card_eq_one_iff_exists.mpr ⟨1,hunit⟩
      exact_mod_cast hu
  | @insert p s hps ih =>
      have hp' := hp p (Finset.mem_insert_self _ _)
      have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
      have hc : IsCoprime p (∏ q ∈ s,q) := by
        apply IsCoprime.prod_right
        intro q hq
        exact primaryPrimes_isCoprime hp' (hs q hq) (fun heq => hps (heq ▸ hq))
      rw [Finset.prod_insert hps,metaplecticTotient_mul hc,metaplecticTotient_prime hp',
        ih hs,Finset.prod_insert hps]

lemma metaplecticTotient_density {r : Eisenstein} (hr : primary r) (hsr : Squarefree r) :
    metaplecticTotient r/norm r =
      ∏ p ∈ primaryPrimeFactors r,(1-(norm p)⁻¹) := by
  have hp : ∀ p ∈ primaryPrimeFactors r, primaryPrime p :=
    fun p hp => (primaryPrimeFactor_spec hr hp).1
  have hn : (∏ p ∈ primaryPrimeFactors r,norm p) = norm r := by
    rw [←norm_finset_prod,primaryPrimeFactors_prod hr hsr]
  have hφ := metaplecticTotient_prod (primaryPrimeFactors r) hp
  rw [primaryPrimeFactors_prod hr hsr] at hφ
  rw [hφ]
  rw [←hn,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp'
  have hnp := norm_pos_of_ne_zero (primary_ne_zero (hp p hp').1)
  field_simp

lemma primary_moebius_density {r : Eisenstein} (hr : primary r) (hsr : Squarefree r) :
    (∑ s ∈ (primaryPrimeFactors r).powerset,
      (idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p)) = metaplecticTotient r/norm r := by
  rw [metaplecticTotient_density hr hsr,Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro s hs
  have hp : ∀ p ∈ s, primaryPrime p := fun p hp =>
    (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1
  rw [idealMoebius_prod_primaryPrimes s hp]
  simp only [Finset.prod_const_one,mul_one]
  rw [Finset.prod_inv_distrib]
  have hn : (∏ p ∈ s,norm p) = norm (∏ p ∈ s,p) := (norm_finset_prod _ _).symm
  rw [hn]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeUnitFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sole zero-frequency contribution of coprime squarefree rows
comes from the literal unit row. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramDualTerm_unit_zero (W : ℝ → ℂ) (Z : ℝ) :
    gramDualTerm 1 1 W Z 0 = normProfileFourier W 0 := by
  simp [gramDualTerm,cubicSymbol_one_lower,tracePair]

lemma coprimePoissonDyad_unit_frequency (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (u : Eisenstein → ℂ) (W : ℝ → ℂ) (Z : ℝ) :
    coprimePoissonDyad S {0} u W Z =
      if (1:Eisenstein) ∈ S then
        u 1*star (u 1)*(Z/9:ℝ)*normProfileFourier W 0 else 0 := by
  let F (a b : Eisenstein) : ℂ := if IsCoprime a b then
    u a*star (u b)*(Z/(9*Real.sqrt (norm (a*b))):ℝ)*(gauss a*star (gauss b))*
      gramDualTerm a b W Z 0 else 0
  have hz (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S)
      (hab1 : ¬(a = 1 ∧ b = 1)) : F a b = 0 := by
    dsimp only [F]
    by_cases hab : IsCoprime a b
    · rw [ite_eq_left hab]
      have hne : a ≠ b := by
        intro he
        have hdiag : IsCoprime a a := by simpa only [← he] using hab
        have hunit : IsUnit a := isCoprime_self.mp hdiag
        have ha1 := primary_unit_eq_one hunit (hS a ha).1
        exact hab1 ⟨ha1,he ▸ ha1⟩
      rw [gramDualTerm_zero (hS a ha).1 (hS b hb).1 (hS a ha).2 (hS b hb).2 hab hne]
      ring
    · exact ite_eq_right hab
  have hval : F 1 1 = u 1*star (u 1)*(Z/9:ℝ)*normProfileFourier W 0 := by
    simp [F,isCoprime_one_left,gramDualTerm_unit_zero,gauss_one,norm]
  unfold coprimePoissonDyad
  simp only [Finset.sum_singleton]
  change (∑ a ∈ S, ∑ b ∈ S, F a b) = _
  by_cases h1 : (1:Eisenstein) ∈ S
  · rw [ite_eq_left h1]
    calc
      _ = ∑ b ∈ S, F 1 b := Finset.sum_eq_single_of_mem 1 h1 (by
        intro a ha ha1
        exact Finset.sum_eq_zero (fun b hb => hz a b ha hb (fun hab => ha1 hab.1)))
      _ = F 1 1 := Finset.sum_eq_single_of_mem 1 h1 (by
        intro b hb hb1
        exact hz 1 b h1 hb (fun hab => hb1 hab.2))
      _ = _ := hval
  · rw [ite_eq_right h1]
    exact Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero
      (fun b hb => hz a b ha hb (fun hab => h1 (hab.1 ▸ ha))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightGramContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the literal variance follows from its finite Gram
identity; the unit square-divisor is exactly the unrestricted variance. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma continuous_dispersionAmplitude (β : Eisenstein → ℂ) (a : Eisenstein) :
    Continuous (fun u => dispersionAmplitude β u a) := by
  unfold dispersionAmplitude
  exact (continuous_const.mul (continuous_normTwist a)).mul continuous_const

lemma continuous_smoothedDispersionVariance (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {A : ℝ} (hA : 0 < A) : Continuous (fun u => smoothedDispersionVariance S β u V A) := by
  simp_rw [smoothedDispersionVariance_gram S hS β _ V hV hV' hA]
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  exact ((continuous_dispersionAmplitude β a).mul (continuous_dispersionAmplitude β b).star).mul continuous_const

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWeightedMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity transfers the actual full-variance height bound to any
finite primary outer set with weight at most one, including μ². -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finite_weighted_dispersion_le (S P : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b) (hP : ∀ a ∈ P, primary a)
    (β : Eisenstein → ℂ) (w : Eisenstein → ℝ) (hw : ∀ a ∈ P, w a ≤ 1)
    (V : ℝ → ℝ) (hV0 : ∀ x, 0 ≤ V x)
    (hV : HasCompactSupport (fun x => (V x:ℂ)))
    (hV' : ContDiff ℝ ∞ (fun x => (V x:ℂ))) {A : ℝ} (hA : 0 < A) (u : ℝ) :
    (∑ a ∈ P, w a*V (norm a/A)*‖dispersionPolynomial S β u a‖^2) ≤
      ‖smoothedDispersionVariance S β u (fun x => (V x:ℂ)) A‖ := by
  let g := fun a : Eisenstein => if primary a then
    V (norm a/A)*‖dispersionPolynomial S β u a‖^2 else 0
  have hs : Summable g := by
    apply Complex.summable_ofReal.mp
    convert summable_restricted_dispersion (fun _ => True) S hS β u
      (fun x => (V x:ℂ)) hV hV' hA using 1
    all_goals try with_reducible_and_instances rfl
    funext a
    dsimp [g]
    split_ifs <;> simp_all
  have heq : smoothedDispersionVariance S β u (fun x => (V x:ℂ)) A = ((∑' a, g a : ℝ):ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro a
    dsimp [smoothedDispersionVariance,g]
    split_ifs <;> simp
  calc
    _ ≤ ∑ a ∈ P, V (norm a/A)*‖dispersionPolynomial S β u a‖^2 := by
      apply Finset.sum_le_sum
      intro a ha
      have hn := mul_nonneg (hV0 (norm a/A)) (sq_nonneg ‖dispersionPolynomial S β u a‖)
      simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right (hw a ha) hn
    _ = ∑ a ∈ P, g a := Finset.sum_congr rfl (fun a ha => by simp [g,hP a ha])
    _ ≤ ∑' a, g a := hs.sum_le_tsum P (fun a _ => by
      dsimp [g]
      split_ifs
      · exact mul_nonneg (hV0 _) (sq_nonneg _)
      · exact le_rfl)
    _ ≤ _ := by rw [heq,Complex.norm_real,Real.norm_eq_abs]; exact le_abs_self _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine Gauss-sum bilinear forms inherit the full height variance
bound by finite Cauchy--Schwarz, retaining the original coefficients. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma bilinear_full_variance_bound_sq (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (V : ℝ → ℝ) (hV0 : ∀ x, 0 ≤ V x)
    (hV : HasCompactSupport (fun x => (V x:ℂ)))
    (hV' : ContDiff ℝ ∞ (fun x => (V x:ℂ))) {A : ℝ} (hA : 0 < A)
    (hPV : ∀ a ∈ P, 1 ≤ V (norm a/A)) :
    ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist u (a*b)‖^2 ≤
      (∑ a ∈ P, ‖α a‖^2)*‖smoothedDispersionVariance S β u (fun x => (V x:ℂ)) A‖ := by
  rw [bilinear_gauss_eq_rows P S α β u hP hS]
  have hrows : (∑ a ∈ P, ‖normTwist u a*gauss a*dispersionPolynomial S β u a‖^2) ≤
      ‖smoothedDispersionVariance S β u (fun x => (V x:ℂ)) A‖ := by
    have hw := finite_weighted_dispersion_le S P hS hP β
      (fun _ => 1) (fun _ _ => le_rfl) V hV0 hV hV' hA u
    apply (Finset.sum_le_sum (g := fun a => V (norm a/A)*‖dispersionPolynomial S β u a‖^2) ?_).trans
      (by simpa only [one_mul] using hw)
    intro a ha
    rw [norm_mul,norm_mul,norm_normTwist,one_mul,mul_pow]
    have hg : ‖gauss a‖^2 ≤ 1 := by nlinarith [norm_gauss_le_one (hP a ha),_root_.norm_nonneg (gauss a)]
    exact mul_le_mul_of_nonneg_right (hg.trans (hPV a ha)) (sq_nonneg _)
  calc
    _ = ‖∑ a ∈ P, α a*(normTwist u a*gauss a*dispersionPolynomial S β u a)‖^2 := by
      congr 2
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ (∑ a ∈ P, ‖α a‖^2)*∑ a ∈ P, ‖normTwist u a*gauss a*dispersionPolynomial S β u a‖^2 :=
      complex_bilinear_rows_sq P α _
    _ ≤ _ := mul_le_mul_of_nonneg_left hrows (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma height_bilinear_full_variance_bound_sq (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (V : ℝ → ℝ) (hV0 : ∀ x, 0 ≤ V x)
    (hV : HasCompactSupport (fun x => (V x:ℂ)))
    (hV' : ContDiff ℝ ∞ (fun x => (V x:ℂ))) {A T : ℝ} (hA : 0 < A) (hT : 0 < T)
    (hPV : ∀ a ∈ P, 1 ≤ V (norm a/A)) :
    dyadicHeightMean (fun t =>
      ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖^2) T ≤
      (∑ a ∈ P, ‖α a‖^2)*dyadicHeightMean
        (fun t => ‖smoothedDispersionVariance S β (u+t) (fun x => (V x:ℂ)) A‖) T := by
  have hc : Continuous (fun t =>
      ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖^2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    exact continuous_const.mul ((continuous_normTwist (a*b)).comp (continuous_const.add continuous_id))
  have hv : Continuous (fun t : ℝ => ‖smoothedDispersionVariance S β (u+t) (fun x => (V x:ℂ)) A‖) :=
    ((continuous_smoothedDispersionVariance S hS β (fun x => (V x:ℂ)) hV hV' hA).comp
    (continuous_const.add continuous_id)).norm
  have hm := dyadicHeightMean_mono hc (continuous_const.mul hv) hT (fun t _ =>
    bilinear_full_variance_bound_sq P S α β (u+t) hP hS V hV0 hV hV' hA hPV)
  exact hm.trans_eq (dyadicHeightMean_const_mul _ _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightBilinearScale
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the genuine height-averaged bilinear estimate. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma dyadicHeightMean_norm_le_of_sq_le {f : ℝ → ℂ} (hf : Continuous f)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ R^2) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤ 2*R := by
  have hm := dyadicHeightMean_mono
    (f := fun t => (2*R)*‖f t‖) (g := fun t => ‖f t‖^2+R^2)
    (continuous_const.mul hf.norm) ((hf.norm.pow 2).add continuous_const) hT
    (fun t _ => by nlinarith [sq_nonneg (‖f t‖-R)])
  rw [dyadicHeightMean_const_mul,
    dyadicHeightMean_add (f := fun t => ‖f t‖^2) (g := fun _ => R^2)
      (hf.norm.pow 2) continuous_const,
    dyadicHeightMean_const _ hT.ne'] at hm
  nlinarith [sq_pos_of_pos hR]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightSquareRoot
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unsquaring a two-sided height mean, including zero coefficient energy. -/
noncomputable section
namespace CubicFirstMoment

lemma dyadicHeightMean_norm_le_of_sq_le_nonneg {f : ℝ → ℂ} (hf : Continuous f)
    {T R : ℝ} (hT : 0 < T) (hR : 0 ≤ R)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ R^2) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤ 2*R := by
  by_cases hp : 0 < R
  · exact dyadicHeightMean_norm_le_of_sq_le hf hT hp hsq
  have hz : R = 0 := le_antisymm (le_of_not_gt hp) hR
  subst R
  by_contra hh
  have hm : 0 < dyadicHeightMean (fun t => ‖f t‖) T := by linarith
  have hb := dyadicHeightMean_norm_le_of_sq_le hf hT
    (R := dyadicHeightMean (fun t => ‖f t‖) T/4) (by positivity)
    (hsq.trans (by nlinarith [sq_nonneg (dyadicHeightMean (fun t => ‖f t‖) T/4)]))
  linarith

lemma dyadicHeightMean_norm_le_sqrt {f : ℝ → ℂ} (hf : Continuous f)
    {T R : ℝ} (hT : 0 < T) (hR : 0 ≤ R)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ R) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤ 2*Real.sqrt R := by
  exact dyadicHeightMean_norm_le_of_sq_le_nonneg hf hT (Real.sqrt_nonneg _)
    (by rwa [Real.sq_sqrt hR])

lemma height_cell_square_root {f : ℝ → ℂ} (hf : Continuous f)
    {T K D E a b : ℝ} (hT : 0 < T) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ K*(D+E)*a*b) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤
      2*Real.sqrt K*(Real.sqrt D+Real.sqrt E)*Real.sqrt a*Real.sqrt b := by
  have hh := dyadicHeightMean_norm_le_sqrt hf hT (by positivity : 0 ≤ K*(D+E)*a*b) hsq
  rw [Real.sqrt_mul (by positivity : 0 ≤ K*(D+E)*a),
    Real.sqrt_mul (by positivity : 0 ≤ K*(D+E)),Real.sqrt_mul hK] at hh
  have he : Real.sqrt (D+E) ≤ Real.sqrt D+Real.sqrt E := by
    nlinarith [Real.sq_sqrt (add_nonneg hD hE),Real.sq_sqrt hD,Real.sq_sqrt hE,
      Real.sqrt_nonneg (D+E),Real.sqrt_nonneg D,Real.sqrt_nonneg E,
      mul_nonneg (Real.sqrt_nonneg D) (Real.sqrt_nonneg E)]
  apply hh.trans
  nlinarith [mul_nonneg (show 0 ≤ 2*Real.sqrt K*Real.sqrt a*Real.sqrt b by positivity)
    (sub_nonneg.mpr he)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramSeminormControl
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite seminorm control of the actual radial composition operator.
The constant is chosen before the test profile, as required for shrinking cells. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

theorem schwartz_wideGramExp_comp_seminorm (M : ℝ) (hM : 0 ≤ M) (n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : 𝓢(ℂ, ℂ)) (c : ℝ), 0 ≤ c → ∀ u : ℝ, |u| ≤ 2*M →
      (1+c)^K * ‖iteratedFDeriv ℝ n (fun v => F (c • gramExp v)) u‖ ≤
        C*((Finset.Iic (n+K,n)).sup
          (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) F := by
  obtain ⟨D, hD, hderiv⟩ := wideGramExp_deriv_bound M n
  refine ⟨(n.factorial:ℝ)*(Real.exp M)^(n+K)*2^(n+K)*D^n,by positivity,?_⟩
  intro F c hc u hu
  let L := n+K
  let S := (Finset.Iic (L,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  let H := (Real.exp M)^L * 2^L * S
  have hS : 0 ≤ S := by positivity
  have hH : 0 ≤ H := by positivity
  have hc1 : 0 < 1+c := by positivity
  have hC (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ ≤ H / (1+c)^L := by
    rw [le_div_iff₀' (pow_pos hc1 L)]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (L,n)) (k := L) (n := i) (le_refl L) hi F (c • gramExp u)
    calc
      _ ≤ (Real.exp M * (1+‖c • gramExp u‖))^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ := by
        gcongr
        exact wideGramExp_scale_growth hM hc hu
      _ = (Real.exp M)^L * ((1+‖c • gramExp u‖)^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖) := by rw [mul_pow]; ring
      _ ≤ (Real.exp M)^L * (2^L*S) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = H := by dsimp [H]; ring
  have hDb (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun v => c • gramExp v) u‖ ≤ ((1+c)*D)^i := by
    rw [iteratedFDeriv_const_smul_apply' (gramExp_contDiff.of_le (mod_cast le_top)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      _ ≤ c*D := mul_le_mul_of_nonneg_left (hderiv i hin u hu) hc
      _ ≤ (1+c)*D := by nlinarith
      _ ≤ ((1+c)*D)^i := le_self_pow₀ (by nlinarith) (by omega)
  have hb := norm_iteratedFDeriv_comp_le (F.smooth ⊤) (gramExp_contDiff.const_smul c)
    (n := n) (mod_cast le_top) u hC hDb
  calc
    _ ≤ (1+c)^K * ((n.factorial : ℝ)*(H/(1+c)^L)*((1+c)*D)^n) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (n.factorial : ℝ)*H*D^n := by
      dsimp [L]
      rw [pow_add, mul_pow]
      field_simp

    _ = _ := by dsimp [H,S,L]; ring

theorem wideAnnularLogSchwartz_seminorm_control (M : ℝ) (hM : 0 < M) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : 𝓢(ℂ, ℂ)) (c : ℝ), 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (wideAnnularLogSchwartz M hM F c) ≤
        C*((Finset.Iic (n+K,n)).sup
          (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) F := by
  choose C hC hraw using fun i => schwartz_wideGramExp_comp_seminorm M hM.le i K
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) * C (n-i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hC (n-i)).le)
  refine ⟨(2*M)^k*B+1,by positivity,?_⟩
  intro F c hc
  let S := ((Finset.Iic (n+K,n)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hS : 0 ≤ S := by positivity
  have hbound (i : ℕ) (hi : i ≤ n) (u : ℝ) (hu : |u| ≤ 2*M) :
      (1+c)^K*‖iteratedFDeriv ℝ i (fun v => F (c • gramExp v)) u‖ ≤ C i*S := by
    apply (hraw i F c hc u hu).trans
    apply mul_le_mul_of_nonneg_left _ (hC i).le
    have hsub : Finset.Iic (i+K,i) ⊆ Finset.Iic (n+K,n) := by
      intro p hp
      exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp)
        ⟨Nat.add_le_add_right hi K,hi⟩)
    exact Seminorm.le_def.mp (show
      ((Finset.Iic (i+K,i)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) ≤
      (Finset.Iic (n+K,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) from
        Finset.sup_mono hsub) F
  have hfinal : (1+c)^K*SchwartzMap.seminorm ℝ k n (wideAnnularLogSchwartz M hM F c) ≤
      (2*M)^k*B*S := by
    have hp : 0 < (1+c)^K := pow_pos (by positivity) _
    rw [← le_div_iff₀' hp]
    apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
    intro u
    by_cases hu : |u| ≤ 2*M
    · rw [le_div_iff₀' hp]
      have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (wideGramLogBump M hM).contDiff
        ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)) u (n := n) (mod_cast le_top)
      have hd' : (1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖ ≤ B*S := by
        calc
          _ ≤ (1+c)^K * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
                ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖ :=
            mul_le_mul_of_nonneg_left hd hp.le
          _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
                ((1+c)^K * ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ ≤ B*S := by
            rw [show B*S = ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*
            SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM)*C (n-i)*S by
              dsimp [B]; rw [Finset.sum_mul]]
            apply Finset.sum_le_sum
            intro i hi
            have hb : ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ ≤
                SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) := by
              have hb := SchwartzMap.le_seminorm ℝ 0 i (wideGramBumpSchwartz M hM) u
              rw [show (wideGramBumpSchwartz M hM : ℝ → ℝ) = ((wideGramLogBump M hM) : ℝ → ℝ) from rfl] at hb
              simpa only [pow_zero, one_mul] using hb
            simpa only [mul_assoc] using mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity))
              (hbound (n-i) (Nat.sub_le _ _) u hu) (by positivity) (by positivity)
      calc
        _ = ‖u‖^k * ((1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖) := by ring
        _ ≤ (2*M)^k * (B*S) := mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _)
          (by simpa only [Real.norm_eq_abs] using hu) k) hd' (by positivity) (by positivity)
        _ = _ := by ring
    · rw [wideAnnularLogSchwartz_deriv_zero M hM F c u n hu, norm_zero, mul_zero]
      positivity
  exact hfinal.trans (mul_le_mul_of_nonneg_right (by linarith) hS)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormFourierSeminorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite seminorm control survives the norm-denominator multiplier
and Fourier transform, uniformly before choosing a shrinking profile. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem normDenominatorFourier_seminorm_control (M : ℝ) (hM : 0 < M) (k n K : ℕ) :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (F : 𝓢(ℂ,ℂ)) (c : ℝ), 0 ≤ c →
      (1+c)^K*SchwartzMap.seminorm ℝ k n
        (𝓕 (SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
          (wideAnnularLogSchwartz M hM F c))) ≤
        C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F := by
  let A : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ)).comp
      ((SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)).restrictScalars ℝ)
  let p := schwartzSeminormFamily ℝ ℝ ℂ
  let q := (SchwartzMap.seminorm ℝ k n).comp A.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (k,n)).comp A.continuous
  obtain ⟨s,C,hC,hA⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  choose D hD hwide using fun i : ℕ × ℕ =>
    wideAnnularLogSchwartz_seminorm_control M hM i.1 i.2 K
  let I := s.biUnion (fun i => Finset.Iic (i.2+K,i.2))
  let E := 1+∑ i ∈ s, D i
  have hE : 0 < E := by
    have hs : 0 ≤ ∑ i ∈ s, D i := Finset.sum_nonneg (fun i _ => (hD i).le)
    dsimp [E]
    linarith
  refine ⟨I,(C:ℝ)*E,mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)) hE,?_⟩
  intro F c hc
  let B := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp : 0 < (1+c)^K := by positivity
  have hi (i : ℕ × ℕ) (his : i ∈ s) :
      (1+c)^K*(p i) (wideAnnularLogSchwartz M hM F c) ≤ E*B := by
    have hsub : Finset.Iic (i.2+K,i.2) ⊆ I := by
      intro m hm
      exact Finset.mem_biUnion.mpr ⟨i,his,hm⟩
    have hb := Seminorm.le_def.mp (show
        (Finset.Iic (i.2+K,i.2)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ≤
          I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) from Finset.sup_mono hsub) F
    have hd : D i ≤ E := by
      have hh := Finset.single_le_sum (fun j _ => (hD j).le) his
      dsimp [E]
      linarith
    exact (hwide i F c hc).trans ((mul_le_mul_of_nonneg_left hb (hD i).le).trans
      (mul_le_mul_of_nonneg_right hd hB))
  have hsup : (1+c)^K*(s.sup p) (wideAnnularLogSchwartz M hM F c) ≤ E*B := by
    rw [←le_div_iff₀' hp]
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i his
    exact (le_div_iff₀' hp).mpr (hi i his)
  have ht := Seminorm.le_def.mp hA (wideAnnularLogSchwartz M hM F c)
  change SchwartzMap.seminorm ℝ k n (A (wideAnnularLogSchwartz M hM F c)) ≤
    (C:ℝ)*(s.sup p) (wideAnnularLogSchwartz M hM F c) at ht
  calc
    _ ≤ (1+c)^K*((C:ℝ)*(s.sup p) (wideAnnularLogSchwartz M hM F c)) :=
      mul_le_mul_of_nonneg_left ht hp.le
    _ = (C:ℝ)*((1+c)^K*(s.sup p) (wideAnnularLogSchwartz M hM F c)) := by ring
    _ ≤ (C:ℝ)*(E*B) := mul_le_mul_of_nonneg_left hsup C.coe_nonneg
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormProfileOperator
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed radial lift and trace Fourier transform form a continuous
linear operator. Thus the finite profile cost is controlled by finitely
many seminorms of the original one-dimensional cutoff. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap FourierTransform
namespace CubicFirstMoment
open CubicPoisson

lemma normProfileFourierCLM_apply (V : 𝓢(ℝ,ℂ)) (hV : HasCompactSupport (V : ℝ → ℂ)) :
    normProfileFourierCLM V = normProfileFourierSchwartz V hV (V.smooth ⊤) := by
  have he : normProfileLiftCLM V = normProfileSchwartz V hV (V.smooth ⊤) 1 (by norm_num) := by
    ext z
    simp only [normProfileLiftCLM,SchwartzMap.compCLM_apply,Function.comp_apply,
      normProfileSchwartz_apply,div_one]
  change (2/Real.sqrt 3 : ℝ) • traceFourierSchwartz (normProfileLiftCLM V) = _
  rw [he]
  ext z
  rfl

theorem normProfileFourier_finite_seminorm (I : Finset (ℕ × ℕ)) :
    ∃ (J : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ V : 𝓢(ℝ,ℂ),
      (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) (normProfileFourierCLM V) ≤
        C*(J.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) V := by
  let q : Seminorm ℝ 𝓢(ℂ,ℂ) := I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)
  have hq : Continuous q := Seminorm.continuous_finsetSup
    (fun i _ => (schwartz_withSeminorms ℝ ℂ ℂ).continuous_seminorm i)
  obtain ⟨J,C,hC,hb⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ)
    (q.comp normProfileFourierCLM.toLinearMap) (hq.comp normProfileFourierCLM.continuous)
  refine ⟨J,C,NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC),?_⟩
  intro V
  exact Seminorm.le_def.mp hb V

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShrinkingProfile
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial seminorm costs for affine shrinking of a fixed cutoff. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

lemma iteratedFDeriv_comp_sub_real (f : ℝ → ℂ) (c : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => f (x-c)) = fun x => iteratedFDeriv ℝ n f (x-c) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    funext x
    simp only [iteratedFDeriv_succ_eq_comp_left,ih,Function.comp_apply,fderiv_comp_sub]

lemma affineSchwartzProfile_deriv_norm (f : 𝓢(ℝ,ℂ)) (J c : ℝ) (hJ : J ≠ 0)
    (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (affineSchwartzProfile f J c hJ) x‖ =
      |J|^n*‖iteratedFDeriv ℝ n f (J*(x-c))‖ := by
  have he : (affineSchwartzProfile f J c hJ : ℝ → ℂ) = fun x => (fun y => f (J • y)) (x-c) := rfl
  rw [he,iteratedFDeriv_comp_sub_real (fun y => f (J • y)) c n,
    iteratedFDeriv_comp_const_smul J (f.smooth n),
    norm_smul,Real.norm_eq_abs,abs_pow]
  rfl

theorem affineSchwartzProfile_seminorm (f : 𝓢(ℝ,ℂ)) {J c : ℝ}
    (hJ : 1 ≤ J) (hc : |c| ≤ 2) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (affineSchwartzProfile f J c (by linarith)) ≤
      6^k*J^n*((Finset.Iic (k,n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) f := by
  have hJ0 : 0 < J := by linarith
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro x
  rw [affineSchwartzProfile_deriv_norm,abs_of_pos hJ0]
  have hx : ‖x‖ ≤ 3*(1+‖J*(x-c)‖) := by
    have htri := norm_add_le (x-c) c
    have hh : ‖x-c‖ ≤ J*‖x-c‖ := le_mul_of_one_le_left (_root_.norm_nonneg _) hJ
    rw [norm_mul,Real.norm_of_nonneg hJ0.le]
    rw [sub_add_cancel] at htri
    have hc' : ‖c‖ ≤ 2 := by simpa only [Real.norm_eq_abs] using hc
    nlinarith [_root_.norm_nonneg (x-c)]
  have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (k,n)) (k := k) (n := n) (le_refl _) (le_refl _) f (J*(x-c))
  calc
    _ ≤ (3*(1+‖J*(x-c)‖))^k*(J^n*‖iteratedFDeriv ℝ n f (J*(x-c))‖) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (_root_.norm_nonneg _) hx k) (by positivity)
    _ = (3^k*J^n)*((1+‖J*(x-c)‖)^k*‖iteratedFDeriv ℝ n f (J*(x-c))‖) := by
      rw [mul_pow]
      ring
    _ ≤ (3^k*J^n)*(2^k*((Finset.Iic (k,n)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) f) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [show (6:ℝ)^k = 3^k*2^k by rw [←mul_pow]; norm_num]; ring

/-- Every fixed finite family of seminorms has a polynomial shrinking cost. -/
theorem affineSchwartzProfile_finite_cost (f : 𝓢(ℝ,ℂ)) (I : Finset (ℕ × ℕ)) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧ ∀ (J c : ℝ) (hJ : 1 ≤ J), |c| ≤ 2 →
      (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
        (affineSchwartzProfile f J c (by linarith)) ≤ K*J^d := by
  classical
  let d := I.sup Prod.snd
  let a (m : ℕ × ℕ) := (6:ℝ)^m.1 *
    ((Finset.Iic m).sup (fun j => SchwartzMap.seminorm ℝ j.1 j.2)) f
  let K := 1+∑ m ∈ I, a m
  have ha (m : ℕ × ℕ) : 0 ≤ a m := by dsimp [a]; positivity
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (fun m (_ : m ∈ I) => ha m)
    dsimp [K]
    linarith
  refine ⟨d,K,hK,?_⟩
  intro J c hJ hc
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro m hm
  have hn : m.2 ≤ d := Finset.le_sup (f := Prod.snd) hm
  have hmK : a m ≤ K := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ I) => ha j) hm
    dsimp [K]
    linarith
  calc
    _ ≤ 6^m.1*J^m.2*((Finset.Iic m).sup
        (fun j => SchwartzMap.seminorm ℝ j.1 j.2)) f :=
      affineSchwartzProfile_seminorm f hJ hc m.1 m.2
    _ = a m*J^m.2 := by dsimp [a]; ring
    _ ≤ K*J^d := mul_le_mul hmK (pow_le_pow_right₀ hJ hn) (by positivity) hK.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonZeroMode
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero mode in a common-factor block is a single original row.
Its signed Möbius sum is the exact finite coprimality density. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_moebius_density_bounds {k : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) :
    0 ≤ metaplecticTotient k/norm k ∧ metaplecticTotient k/norm k ≤ 1 := by
  rw [metaplecticTotient_density hk hsk]
  have hp (p : Eisenstein) (h : p ∈ primaryPrimeFactors k) :
      0 ≤ 1-(norm p)⁻¹ ∧ 1-(norm p)⁻¹ ≤ 1 := by
    have hn := one_le_norm (primaryPrimeFactor_spec hk h).1.2.ne_zero
    constructor
    · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hn)
    · have : 0 ≤ (norm p)⁻¹ := by positivity
      linarith
  exact ⟨Finset.prod_nonneg (fun p h => (hp p h).1),
    Finset.prod_le_one (fun p h => (hp p h).1) (fun p h => (hp p h).2)⟩

lemma commonGramZeroMode_eq (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (v : Eisenstein → ℂ)
    (W : ℝ → ℂ) (A : ℝ) {k : Eisenstein} (hk : primary k) (hsk : Squarefree k) :
    commonGramZeroMode S v W A k = if k ∈ S then
      v k*star (v k)*(A/9:ℝ)*normProfileFourier W 0*
        (metaplecticTotient k/norm k:ℝ) else 0 := by
  have hr := residualRows_primary hk hS
  have hmem : (1:Eisenstein) ∈ residualRows S k ↔ k ∈ S := by
    rw [mem_residualRows (primary_ne_zero hk),mul_one]
  unfold commonGramZeroMode
  simp_rw [coprimePoissonDyad_unit_frequency _ hr,hmem]
  by_cases hks : k ∈ S
  · simp only [ite_eq_left hks]
    calc
      _ = (v k*star (v k)*(A/9:ℝ)*normProfileFourier W 0)*
          (((∑ s ∈ (primaryPrimeFactors k).powerset,
            (idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p)):ℝ):ℂ) := by
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        simp only [commonBlockCoefficient,mul_one,cubicSymbol_one_lower,mul_one]
        ring
      _ = _ := by rw [primary_moebius_density hk hsk]
  · simp only [ite_eq_right hks,mul_zero,Finset.sum_const_zero]

lemma commonGramZeroMode_norm_le (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (v : Eisenstein → ℂ)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) {k : Eisenstein}
    (hk : primary k) (hsk : Squarefree k) :
    ‖commonGramZeroMode S v W A k‖ ≤
      if k ∈ S then (‖normProfileFourier W 0‖/9)*A*‖v k‖^2 else 0 := by
  rw [commonGramZeroMode_eq S hS v W A hk hsk]
  split_ifs
  · rw [norm_mul,norm_mul,norm_mul,norm_mul,norm_star,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ A/9),
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primary_moebius_density_bounds hk hsk).1]
    calc
      _ ≤ ‖v k‖*‖v k‖*(A/9)*‖normProfileFourier W 0‖*1 :=
        mul_le_mul_of_nonneg_left (primary_moebius_density_bounds hk hsk).2
          (show 0 ≤ ‖v k‖*‖v k‖*(A/9)*‖normProfileFourier W 0‖ by positivity)
      _ = _ := by ring
  · simp only [norm_zero,le_refl]

lemma commonGramZeroMode_sum_bound (S K : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hK : ∀ k ∈ K, primary k ∧ Squarefree k) (v : Eisenstein → ℂ)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    ‖∑ k ∈ K, commonGramZeroMode S v W A k‖ ≤
      (‖normProfileFourier W 0‖/9)*A*∑ a ∈ S, ‖v a‖^2 := by
  let c := (‖normProfileFourier W 0‖/9)*A
  have hc : 0 ≤ c := by dsimp [c]; positivity
  calc
    _ ≤ ∑ k ∈ K, ‖commonGramZeroMode S v W A k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ K, if k ∈ S then c*‖v k‖^2 else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      exact commonGramZeroMode_norm_le S hS v W hA (hK k hk).1 (hK k hk).2
    _ = ∑ k ∈ K.filter (fun k => k ∈ S), c*‖v k‖^2 :=
      (Finset.sum_filter (s := K) (fun k => k ∈ S) (fun k => c*‖v k‖^2)).symm
    _ ≤ ∑ k ∈ S, c*‖v k‖^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (fun k hk => (Finset.mem_filter.mp hk).2)
      intro k hk hnot
      positivity
    _ = _ := by rw [← Finset.mul_sum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormMellinSeminorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-profile control of the actual full Mellin-line moments. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace CubicFirstMoment

theorem normDenominatorMellinCoefficient_moment_control (M : ℝ) (hM : 0 < M) (A B : ℕ) :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
        (ρ : ℝ), 0 ≤ ρ →
      (1+ρ)^A*(∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤
        C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierSchwartz W hW hW') := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k*∫ t : ℝ, (1+‖t‖)^(-(k:ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))
  obtain ⟨I₀,C₀,hC₀,h₀⟩ := normDenominatorFourier_seminorm_control M hM 0 0 (2*A)
  obtain ⟨I₁,C₁,hC₁,h₁⟩ := normDenominatorFourier_seminorm_control M hM (B+k) 0 (2*A)
  let I := I₀ ∪ I₁
  refine ⟨I,D*(C₀+C₁)+1,by positivity,?_⟩
  intro W hW hW' ρ hρ
  let F := normProfileFourierSchwartz W hW hW'
  let S := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have h := (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integral_pow_mul_iteratedFDeriv_le ℝ volume B 0
  simp only [norm_iteratedFDeriv_zero] at h
  have hsup₀ : (I₀.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) F
  have hsup₁ : (I₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) F
  have hc₀ := (h₀ F (Real.sqrt ρ) (Real.sqrt_nonneg ρ)).trans
    (mul_le_mul_of_nonneg_left hsup₀ hC₀.le)
  have hc₁ := (h₁ F (Real.sqrt ρ) (Real.sqrt_nonneg ρ)).trans
    (mul_le_mul_of_nonneg_left hsup₁ hC₁.le)
  rw [←normDenominatorLogSchwartz_eq_annular] at hc₀ hc₁
  calc
    _ ≤ (1+Real.sqrt ρ)^(2*A)*(D*
        (SchwartzMap.seminorm ℝ 0 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
         SchwartzMap.seminorm ℝ (B+k) 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)))) :=
      mul_le_mul hs h (integral_nonneg (fun _ => by positivity)) (by positivity)
    _ = D*((1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ 0 0
        (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
      (1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ (B+k) 0
        (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))) := by ring
    _ ≤ D*(C₀*S+C₁*S) := mul_le_mul_of_nonneg_left (add_le_add hc₀ hc₁) hD
    _ ≤ (D*(C₀+C₁)+1)*S := by nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideMellinControl
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Finite seminorm control survives the norm-denominator multiplier
and Fourier transform, uniformly before choosing a shrinking profile. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem wideGramFourier_seminorm_control (M : ℝ) (hM : 0 < M) (k n K : ℕ) :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (F : 𝓢(ℂ,ℂ)) (c : ℝ), 0 ≤ c →
      (1+c)^K*SchwartzMap.seminorm ℝ k n
        (𝓕 (wideAnnularLogSchwartz M hM F c)) ≤
        C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F := by
  let A : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ)
  let p := schwartzSeminormFamily ℝ ℝ ℂ
  let q := (SchwartzMap.seminorm ℝ k n).comp A.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (k,n)).comp A.continuous
  obtain ⟨s,C,hC,hA⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  choose D hD hwide using fun i : ℕ × ℕ =>
    wideAnnularLogSchwartz_seminorm_control M hM i.1 i.2 K
  let I := s.biUnion (fun i => Finset.Iic (i.2+K,i.2))
  let E := 1+∑ i ∈ s, D i
  have hE : 0 < E := by
    have hs : 0 ≤ ∑ i ∈ s, D i := Finset.sum_nonneg (fun i _ => (hD i).le)
    dsimp [E]
    linarith
  refine ⟨I,(C:ℝ)*E,mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)) hE,?_⟩
  intro F c hc
  let B := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp : 0 < (1+c)^K := by positivity
  have hi (i : ℕ × ℕ) (his : i ∈ s) :
      (1+c)^K*(p i) (wideAnnularLogSchwartz M hM F c) ≤ E*B := by
    have hsub : Finset.Iic (i.2+K,i.2) ⊆ I := by
      intro m hm
      exact Finset.mem_biUnion.mpr ⟨i,his,hm⟩
    have hb := Seminorm.le_def.mp (show
        (Finset.Iic (i.2+K,i.2)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ≤
          I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) from Finset.sup_mono hsub) F
    have hd : D i ≤ E := by
      have hh := Finset.single_le_sum (fun j _ => (hD j).le) his
      dsimp [E]
      linarith
    exact (hwide i F c hc).trans ((mul_le_mul_of_nonneg_left hb (hD i).le).trans
      (mul_le_mul_of_nonneg_right hd hB))
  have hsup : (1+c)^K*(s.sup p) (wideAnnularLogSchwartz M hM F c) ≤ E*B := by
    rw [←le_div_iff₀' hp]
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i his
    exact (le_div_iff₀' hp).mpr (hi i his)
  have ht := Seminorm.le_def.mp hA (wideAnnularLogSchwartz M hM F c)
  change SchwartzMap.seminorm ℝ k n (A (wideAnnularLogSchwartz M hM F c)) ≤
    (C:ℝ)*(s.sup p) (wideAnnularLogSchwartz M hM F c) at ht
  calc
    _ ≤ (1+c)^K*((C:ℝ)*(s.sup p) (wideAnnularLogSchwartz M hM F c)) :=
      mul_le_mul_of_nonneg_left ht hp.le
    _ = (C:ℝ)*((1+c)^K*(s.sup p) (wideAnnularLogSchwartz M hM F c)) := by ring
    _ ≤ (C:ℝ)*(E*B) := mul_le_mul_of_nonneg_left hsup C.coe_nonneg
    _ = _ := by dsimp [B]; ring



theorem wideGramMellinCoefficient_moment_control (M : ℝ) (hM : 0 < M) (A B : ℕ) :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
        (ρ : ℝ), 0 ≤ ρ →
      (1+ρ)^A*(∫ t : ℝ, ‖t‖^B*‖wideGramMellinCoefficient M hM W hW hW' ρ t‖) ≤
        C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierSchwartz W hW hW') := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k*∫ t : ℝ, (1+‖t‖)^(-(k:ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))
  obtain ⟨I₀,C₀,hC₀,h₀⟩ := wideGramFourier_seminorm_control M hM 0 0 (2*A)
  obtain ⟨I₁,C₁,hC₁,h₁⟩ := wideGramFourier_seminorm_control M hM (B+k) 0 (2*A)
  let I := I₀ ∪ I₁
  refine ⟨I,D*(C₀+C₁)+1,by positivity,?_⟩
  intro W hW hW' ρ hρ
  let F := normProfileFourierSchwartz W hW hW'
  let S := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have h := (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ)).integral_pow_mul_iteratedFDeriv_le ℝ volume B 0
  simp only [norm_iteratedFDeriv_zero] at h
  have hsup₀ : (I₀.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) F
  have hsup₁ : (I₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) F
  have hc₀ := (h₀ F (Real.sqrt ρ) (Real.sqrt_nonneg ρ)).trans
    (mul_le_mul_of_nonneg_left hsup₀ hC₀.le)
  have hc₁ := (h₁ F (Real.sqrt ρ) (Real.sqrt_nonneg ρ)).trans
    (mul_le_mul_of_nonneg_left hsup₁ hC₁.le)
  rw [wideAnnularLogSchwartz_eq_wideGramLogSchwartz] at hc₀ hc₁
  calc
    _ ≤ (1+Real.sqrt ρ)^(2*A)*(D*
        (SchwartzMap.seminorm ℝ 0 0 (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ))+
         SchwartzMap.seminorm ℝ (B+k) 0 (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ)))) :=
      mul_le_mul hs h (integral_nonneg (fun _ => by positivity)) (by positivity)
    _ = D*((1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ 0 0
        (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ))+
      (1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ (B+k) 0
        (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ))) := by ring
    _ ≤ D*(C₀*S+C₁*S) := mul_le_mul_of_nonneg_left (add_le_add hc₀ hc₁) hD
    _ ≤ (D*(C₀+C₁)+1)*S := by nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonProfileBudget
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative profile budget is constructed from finitely many
Schwartz seminorms. It records only the two analytic costs used by the
Poisson argument; it is not an additional published input. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

lemma radialDualProfile_seminorm_control (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (q : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1+t)^q*‖radialDualProfile V t‖ ≤ 2^(2*q)*
      ((Finset.Iic (2*q,0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (normProfileFourierSchwartz V hV hV') := by
  let F := normProfileFourierSchwartz V hV hV'
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2*q,0)) (k := 2*q) (n := 0) (le_refl _) (le_refl _) F (Real.sqrt t : ℂ)
  simp only [norm_iteratedFDeriv_zero] at hb
  have hn : ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs : (1+t)^q ≤ (1+‖(Real.sqrt t : ℂ)‖)^(2*q) := by
    rw [hn,pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt ht,Real.sqrt_nonneg t]
  have he : F (Real.sqrt t : ℂ) = radialDualProfile V t :=
    normProfileFourierSchwartz_apply V hV hV' _
  have hh := mul_le_mul_of_nonneg_right hs (_root_.norm_nonneg (F (Real.sqrt t : ℂ)))
  rw [he] at hh hb
  exact hh.trans hb

/-- Every smooth compact profile has a budget bounded by the same finite
set of derivatives, chosen before the profile. -/
theorem exists_poissonProfileBudget_control :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V),
      ∃ P : PoissonProfileBudget, P.V = V ∧
        P.cost ≤ 1+C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierSchwartz V hV hV') := by
  obtain ⟨I₀,C₀,hC₀,hM⟩ := normDenominatorMellinCoefficient_moment_control
    poissonProfileLogWidth poissonProfileLogWidth_pos 3 0
  obtain ⟨I₁,C₁,hC₁,hW⟩ := wideGramMellinCoefficient_moment_control
    poissonProfileLogWidth poissonProfileLogWidth_pos 3 0
  let J : Finset (ℕ × ℕ) := Finset.Iic (94,0)
  let I := (I₀ ∪ I₁) ∪ J
  let C := C₀+C₁+(2:ℝ)^94
  refine ⟨I,C,by dsimp [C]; positivity,?_⟩
  intro V hV hV'
  let F := normProfileFourierSchwartz V hV hV'
  let S := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hm (ρ : ℝ) (hρ : 0 ≤ ρ) :
      (1+ρ)^3*(∫ s : ℝ, ‖normDenominatorMellinCoefficient poissonProfileLogWidth
        poissonProfileLogWidth_pos V hV hV' ρ s‖) ≤ 1+C*S := by
    have hh := hM V hV hV' ρ hρ
    simp only [pow_zero,one_mul] at hh
    have hs : (I₀.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
      Seminorm.le_def.mp (Finset.sup_mono
        (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)) F
    have hb := hh.trans (mul_le_mul_of_nonneg_left hs hC₀.le)
    dsimp [C]
    nlinarith
  have hr (t : ℝ) (ht : 0 ≤ t) : (1+t)^47*‖radialDualProfile V t‖ ≤ 1+C*S := by
    have hh := radialDualProfile_seminorm_control V hV hV' 47 t ht
    have hsub : J ⊆ I := Finset.subset_union_right
    have hsup : J.sup (fun m => (SchwartzMap.seminorm ℝ m.1 m.2 : Seminorm ℝ 𝓢(ℂ,ℂ))) ≤
        I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) := Finset.sup_mono hsub
    have hs : (J.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
      Seminorm.le_def.mp hsup F
    rw [show (2:ℕ)*47 = 94 by omega] at hh
    dsimp only [J,F] at hs
    have hp : 0 ≤ (2:ℝ)^94 := pow_nonneg (by norm_num) _
    have hb := hh.trans (mul_le_mul_of_nonneg_left hs hp)
    have hcoeff : (2:ℝ)^94 ≤ C := by dsimp [C]; linarith
    exact hb.trans ((mul_le_mul_of_nonneg_right hcoeff hS).trans
      (le_add_of_nonneg_left (by norm_num)))
  have hw (ρ : ℝ) (hρ : 0 ≤ ρ) :
      (1+ρ)^3*(∫ s : ℝ, ‖wideGramMellinCoefficient poissonProfileLogWidth
        poissonProfileLogWidth_pos V hV hV' ρ s‖) ≤ 1+C*S := by
    have hh := hW V hV hV' ρ hρ
    simp only [pow_zero,one_mul] at hh
    have hs : (I₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
      Seminorm.le_def.mp (Finset.sup_mono
        (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)) F
    have hb := hh.trans (mul_le_mul_of_nonneg_left hs hC₁.le)
    dsimp [C]
    nlinarith
  exact ⟨⟨V,hV,hV',1+C*S,by positivity,hm,hr,hw⟩,rfl,le_rfl⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThinAnnulusCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine thin-annulus lattice count. Disjoint half-unit disks
around Eisenstein integers fit inside the thickened annulus. -/
noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma complex_ball_real_volume (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball z r) = r^2*Real.pi := by
  simp only [measureReal_def,Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr,ENNReal.coe_toReal,NNReal.coe_real_pi]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThinZeroMode
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact zero mode scales with the radial cell width. -/
noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma thin_radial_integral_bound (W : ℝ → ℂ) {J : ℝ} (hJ : 0 < J)
    (hW : ∀ x, ‖W x‖ ≤ 1)
    (hsupport : ∀ x, W x ≠ 0 → 1 ≤ x ∧ x ≤ 1+1/J) :
    ‖∫ z : ℂ, W (Complex.normSq z)‖ ≤ Real.pi/J := by
  let R := Real.sqrt (1+1/J)
  let S := closedBall (0:ℂ) R \ ball 0 1
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [one_div_pos.mpr hJ])
  have hm : MeasurableSet S := measurableSet_closedBall.diff measurableSet_ball
  have hfin : volume S ≠ ⊤ := by
    apply measure_ne_top_of_subset sdiff_subset
    rw [Complex.volume_closedBall]
    finiteness
  have hg : Integrable (S.indicator (fun _ : ℂ => (1:ℝ))) :=
    (integrable_indicator_iff hm).mpr (integrableOn_const hfin)
  have hbound : ∀ z : ℂ, ‖W (Complex.normSq z)‖ ≤ S.indicator (fun _ => (1:ℝ)) z := by
    intro z
    by_cases hz : W (Complex.normSq z) = 0
    · rw [hz,norm_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) z
    · have hs := hsupport (Complex.normSq z) hz
      have hzS : z ∈ S := by
        refine ⟨?_,?_⟩
        · change dist z 0 ≤ R
          rw [dist_zero_right]
          have hr := Real.sq_sqrt (show 0 ≤ 1+1/J by positivity)
          rw [Complex.normSq_eq_norm_sq] at hs
          dsimp [R]
          nlinarith [_root_.norm_nonneg z,Real.sqrt_nonneg (1+1/J)]
        · change ¬dist z 0 < 1
          rw [dist_zero_right,Complex.normSq_eq_norm_sq] at *
          nlinarith [_root_.norm_nonneg z]
      simpa only [indicator_of_mem hzS] using hW (Complex.normSq z)
  have harea : volume.real S = Real.pi/J := by
    have hsub : ball (0:ℂ) 1 ⊆ closedBall 0 R :=
      (ball_subset_ball hR1).trans ball_subset_closedBall
    have hcfin : volume (closedBall (0:ℂ) R) ≠ ⊤ := by
      rw [Complex.volume_closedBall]
      finiteness
    rw [show S = closedBall (0:ℂ) R \ ball 0 1 from rfl,
      measureReal_sdiff hsub measurableSet_ball hcfin,complex_ball_real_volume _ (by norm_num)]
    have hcv : volume.real (closedBall (0:ℂ) R) = R^2*Real.pi := by
      simp only [measureReal_def,Complex.volume_closedBall,ENNReal.toReal_mul,
        ENNReal.toReal_pow,ENNReal.toReal_ofReal hR,ENNReal.coe_toReal,NNReal.coe_real_pi]
    rw [hcv,show R^2 = 1+1/J from Real.sq_sqrt (by positivity)]
    ring
  calc
    _ ≤ ∫ z : ℂ, S.indicator (fun _ => (1:ℝ)) z :=
      norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)
    _ = volume.real S := by rw [integral_indicator_const _ hm,smul_eq_mul,mul_one]
    _ = _ := harea

theorem thin_normProfileFourier_zero (W : ℝ → ℂ) {J : ℝ} (hJ : 0 < J)
    (hW : ∀ x, ‖W x‖ ≤ 1)
    (hsupport : ∀ x, W x ≠ 0 → 1 ≤ x ∧ x ≤ 1+1/J) :
    ‖normProfileFourier W 0‖ ≤ (2*Real.pi/Real.sqrt 3)/J := by
  rw [normProfileFourier,traceFourier_zero,norm_smul,
    Real.norm_of_nonneg (show 0 ≤ 2/Real.sqrt 3 by positivity)]
  apply (mul_le_mul_of_nonneg_left (thin_radial_integral_bound W hJ hW hsupport)
    (show 0 ≤ 2/Real.sqrt 3 by positivity)).trans_eq
  ring

theorem thin_varianceZeroMode_bound (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) (β : Eisenstein → ℂ)
    (W : ℝ → ℂ) {A J : ℝ} (hA : 0 ≤ A) (hJ : 0 < J)
    (hW : ∀ x, ‖W x‖ ≤ 1)
    (hsupport : ∀ x, W x ≠ 0 → 1 ≤ x ∧ x ≤ 1+1/J) :
    ‖varianceZeroMode S β W A‖ ≤
      (2*Real.pi/(9*Real.sqrt 3))*(A/J)*∑ b ∈ S, ‖β b‖^2 := by
  have hb := commonGramZeroMode_sum_bound S (commonRowFactors S) hS
    (fun k hk => commonRowFactors_spec hS hk) (fun b => star (β b)) W hA
  simp only [norm_star] at hb
  apply hb.trans
  have ht := div_le_div_of_nonneg_right (thin_normProfileFourier_zero W hJ hW hsupport)
    (by norm_num : (0:ℝ) ≤ 9)
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ht hA) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans_eq
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShrinkingVariance
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform small-B remainder for a fixed cutoff narrowed at any polynomial scale. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

lemma affineSchwartzProfile_compact (f : 𝓢(ℝ,ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) (J c : ℝ) (hJ : J ≠ 0) :
    HasCompactSupport (affineSchwartzProfile f J c hJ : ℝ → ℂ) := by
  have hh := (hf.comp_smul hJ).comp_homeomorph (Homeomorph.addRight (-c))
  change HasCompactSupport (fun x => f (J*(x+(-c)))) at hh
  change HasCompactSupport (fun x => f (J*(x-c)))
  simpa only [sub_eq_add_neg] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThinCellCutoff
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual nonnegative cutoff supported in a cell of width 1/J,
with a plateau on the central half of that cell. -/
noncomputable section
open Set Metric
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

lemma thinBaseSchwartz_compact : HasCompactSupport (thinBaseSchwartz : ℝ → ℂ) :=
  thinBaseBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

lemma thinCellCutoff_nonneg (J x : ℝ) : 0 ≤ thinCellCutoff J x := thinBaseBump.nonneg

lemma thinCellCutoff_le_one (J x : ℝ) : thinCellCutoff J x ≤ 1 := thinBaseBump.le_one

lemma thinCellCutoff_eq_affine (J : ℝ) (hJ : J ≠ 0) :
    (fun x => (thinCellCutoff J x : ℂ)) =
      affineSchwartzProfile thinBaseSchwartz J (1+1/(2*J)) hJ := rfl

lemma thinCellCutoff_compact (J : ℝ) (hJ : J ≠ 0) :
    HasCompactSupport (fun x => (thinCellCutoff J x : ℂ)) := by
  rw [thinCellCutoff_eq_affine J hJ]
  exact affineSchwartzProfile_compact thinBaseSchwartz thinBaseSchwartz_compact J _ hJ

lemma thinCellCutoff_smooth (J : ℝ) (hJ : J ≠ 0) :
    ContDiff ℝ ∞ (fun x => (thinCellCutoff J x : ℂ)) := by
  rw [thinCellCutoff_eq_affine J hJ]
  exact (affineSchwartzProfile thinBaseSchwartz J _ hJ).smooth ⊤

lemma thinCellCutoff_norm (J x : ℝ) : ‖(thinCellCutoff J x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_of_nonneg (thinCellCutoff_nonneg J x)]
  exact thinCellCutoff_le_one J x

lemma thinCellCutoff_support {J : ℝ} (hJ : 0 < J) (x : ℝ)
    (hx : (thinCellCutoff J x : ℂ) ≠ 0) : 1 ≤ x ∧ x ≤ 1+1/J := by
  have hm : J*(x-(1+1/(2*J))) ∈ Function.support thinBaseBump := by
    change thinBaseBump _ ≠ 0
    exact fun h => hx (by change (thinBaseBump _ : ℂ) = 0; rw [h]; rfl)
  rw [thinBaseBump.support_eq] at hm
  have ha : |J*(x-(1+1/(2*J)))| < 1/2 := by
    simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,thinBaseBump] using hm
  have hh := abs_lt.mp ha
  have hc : J*(1+1/(2*J)) = J+1/2 := by field_simp
  have hd : J*(1+1/J) = J+1 := by field_simp
  constructor
  · nlinarith
  · nlinarith

lemma thinCellCutoff_one {J x : ℝ} (hJ : 0 < J)
    (hx : 1+1/(4*J) ≤ x ∧ x ≤ 1+3/(4*J)) : thinCellCutoff J x = 1 := by
  apply thinBaseBump.one_of_mem_closedBall
  change dist (J*(x-(1+1/(2*J)))) 0 ≤ 1/4
  rw [dist_zero_right,Real.norm_eq_abs]
  have hc : J*(1+1/(2*J)) = J+1/2 := by field_simp
  have hl : J*(1+1/(4*J)) = J+1/4 := by field_simp
  have hu : J*(1+3/(4*J)) = J+3/4 := by field_simp
  have hxl := mul_le_mul_of_nonneg_left hx.1 hJ.le
  have hxu := mul_le_mul_of_nonneg_left hx.2 hJ.le
  apply abs_le.mpr
  constructor <;> nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogCellMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete dispersion majorant for each actual log-norm cell. The
cell is contained in the plateau of a cutoff at a comparable scale. -/
noncomputable section
namespace CubicFirstMoment

lemma exp_inv_le_one_add {J : ℝ} (hJ : 2 ≤ J) :
    Real.exp (1/J) ≤ 1+2/J := by
  have hJp : 0 < J := by linarith
  have hr : 0 ≤ 1/J := by positivity
  have hrh : 1/J ≤ 1/2 := (div_le_div_iff₀ hJp (by norm_num)).mpr (by linarith)
  have hr1 : 1/J < 1 := by linarith
  apply (Real.exp_bound_div_one_sub_of_interval hr hr1).trans
  apply (div_le_iff₀ (sub_pos.mpr hr1)).mpr
  have hn := mul_nonneg hr (show 0 ≤ 1-2*(1/J) by linarith)
  simp only [div_eq_mul_inv,one_mul] at *
  nlinarith

lemma logCellScale_pos {J A : ℝ} (hJ : 0 < J) (hA : 0 < A) (i : ℤ) :
    0 < logCellScale J A i := by unfold logCellScale; positivity

lemma log_cell_plateau {x A J : ℝ} (hx : 0 < x) (hA : 0 < A) (hJ : 8 ≤ J)
    (i : ℤ) (hi : (i:ℝ) ≤ J*Real.log (x/A) ∧
      J*Real.log (x/A) < (i:ℝ)+1) :
    1+1/(4*(J/8)) ≤ x/logCellScale J A i ∧
      x/logCellScale J A i ≤ 1+3/(4*(J/8)) := by
  have hJp : 0 < J := by linarith
  have he : 0 < Real.exp ((i:ℝ)/J) := Real.exp_pos _
  have hr : 0 < x/A := div_pos hx hA
  have hlo : Real.exp ((i:ℝ)/J) ≤ x/A := by
    rw [←Real.exp_log hr]
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hJp).mpr (by simpa only [mul_comm] using hi.1))
  have hhi : x/A ≤ Real.exp ((i:ℝ)/J)*(1+2/J) := by
    have hlog : Real.log (x/A) < ((i:ℝ)+1)/J :=
      (lt_div_iff₀ hJp).mpr (by simpa only [mul_comm] using hi.2)
    have hh := Real.exp_le_exp.mpr hlog.le
    rw [Real.exp_log hr,show ((i:ℝ)+1)/J = (i:ℝ)/J+1/J by ring,Real.exp_add] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (exp_inv_le_one_add (by linarith)) he.le)
  have hq : 0 ≤ 2/J := by positivity
  have hq1 : 2/J ≤ 1 := (div_le_one hJp).mpr (by linarith)
  have hs : x/logCellScale J A i = (x/A)*(1+2/J)/Real.exp ((i:ℝ)/J) := by
    unfold logCellScale
    field_simp
  have hl : 1+2/J ≤ x/logCellScale J A i := by
    rw [hs]
    apply (le_div_iff₀ he).mpr
    nlinarith
  have hu : x/logCellScale J A i ≤ 1+6/J := by
    rw [hs]
    apply (div_le_iff₀ he).mpr
    have hmul := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 1+2/J by positivity)
    have hsquare : (1+2/J)^2 ≤ 1+6/J := by
      have hh := mul_nonneg hq (sub_nonneg.mpr hq1)
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsquare he.le]
  have he1 : 1/(4*(J/8)) = 2/J := by field_simp; norm_num
  have he3 : 3/(4*(J/8)) = 6/J := by field_simp; norm_num
  simpa only [he1,he3] using And.intro hl hu

lemma logCellScale_bounds {J A Q : ℝ} (hJ : 8 ≤ J) (hA : 0 < A)
    {a : Eisenstein} (ha : primary a) (hn : 1 ≤ norm a/A ∧ norm a/A ≤ Q) :
    A/2 ≤ logCellScale J A (logNormCell J A a) ∧
      logCellScale J A (logNormCell J A a) ≤ Q*A := by
  have hJp : 0 < J := by linarith
  have hp : 0 < 1+2/J := by positivity
  have hd : 1+2/J ≤ 2 := by
    have hh : 2/J ≤ 1 := (div_le_one hJp).mpr (by linarith)
    linarith
  have hi : 0 ≤ logNormCell J A a :=
    Int.floor_nonneg.mpr (mul_nonneg hJp.le (Real.log_nonneg hn.1))
  have hei : 1 ≤ Real.exp ((logNormCell J A a:ℝ)/J) :=
    Real.one_le_exp_iff.mpr (div_nonneg (by exact_mod_cast hi) hJp.le)
  have helo : Real.exp ((logNormCell J A a:ℝ)/J) ≤ norm a/A := by
    rw [←Real.exp_log (div_pos (norm_pos_of_ne_zero (primary_ne_zero ha)) hA)]
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hJp).mpr
      (by simpa only [mul_comm] using (logNormCell_bounds J A a).1))
  unfold logCellScale
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hei hA.le]
  · apply (div_le_iff₀ hp).mpr
    have hQ : 0 ≤ Q := (zero_le_one.trans hn.1).trans hn.2
    have hprod : A*Real.exp ((logNormCell J A a:ℝ)/J) ≤ Q*A := by
      have hh := mul_le_mul_of_nonneg_left (helo.trans hn.2) hA.le
      nlinarith
    have hmore := mul_nonneg (mul_nonneg hQ hA.le) (show 0 ≤ 2/J by positivity)
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogCellNearHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of the actual near-boundary cell polynomials, preserving the
thin diagonal and the proved derivative cost in the dispersion remainder. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma logCellPolynomial_continuous (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B : ℝ) (e : ℤ × ℤ) : Continuous (logCellPolynomial P S α β J A B e) := by
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  exact continuous_const.mul (continuous_normTwist (a*b))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CellHeightIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Fubini for the actual cell polynomials and the height cutoff. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma logCellHeightSum_eq_integral (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (e : ℤ × ℤ) (h : ℝ → ℂ) (hi : Integrable h) :
    logCellHeightSum P S α β J A B X₀ e h =
      ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        logCellPolynomial P S α β J A B e t := by
  let Pi := logNormCellSupport P J A e.1
  let Sj := logNormCellSupport S J B e.2
  let c := fun q : Eisenstein × Eisenstein => α q.1*β q.2*gauss (q.1*q.2)
  let n := fun q : Eisenstein × Eisenstein => q.1*q.2
  calc
    _ = ∑ q ∈ Pi.product Sj, c q*heightFourierIntegral h
        (Real.log (norm (n q))-Real.log X₀) := (Finset.sum_product Pi Sj _).symm
    _ = ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        ∑ q ∈ Pi.product Sj, c q*normTwist t (n q) :=
      height_norm_polynomial_integral _ _ _ h hi _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      exact Finset.sum_product Pi Sj _

lemma logCellHeightIntegrand_integrable (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (e : ℤ × ℤ) (h : ℝ → ℂ) (hi : Integrable h) :
    Integrable (fun t : ℝ => (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
      logCellPolynomial P S α β J A B e t) := by
  have hw : Integrable (fun t : ℝ => h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)) :=
    integrable_height_phase h hi (-Real.log X₀)
  let Pi := logNormCellSupport P J A e.1
  let Sj := logNormCellSupport S J B e.2
  let c := fun q : Eisenstein × Eisenstein => α q.1*β q.2*gauss (q.1*q.2)
  apply hw.mul_bdd (c := ∑ q ∈ Pi.product Sj, ‖c q‖)
    (logCellPolynomial_continuous P S α β J A B e).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have he : (∑ q ∈ Pi.product Sj, c q*normTwist t (q.1*q.2)) =
      logCellPolynomial P S α β J A B e t := Finset.sum_product Pi Sj _
  rw [←he]
  exact norm_indexed_norm_polynomial (Pi.product Sj) c (fun q => q.1*q.2) t

theorem finite_logCellHeightSum_integral (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (E : Finset (ℤ × ℤ)) (h : ℝ → ℂ) (hi : Integrable h) :
    (∑ e ∈ E, logCellHeightSum P S α β J A B X₀ e h) =
      ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        ∑ e ∈ E, logCellPolynomial P S α β J A B e t := by
  simp_rw [logCellHeightSum_eq_integral P S α β J A B X₀ _ h hi]
  rw [←integral_finsetSum E (fun e _ =>
    logCellHeightIntegrand_integrable P S α β J A B X₀ e h hi)]
  apply integral_congr_ae
  filter_upwards with t
  rw [Finset.mul_sum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogLocalizedIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near and far cells reassemble the original Gauss height integral.
This is the high-height, arbitrary-coefficient localization estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma logCellHeightSum_partition (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (h : ℝ → ℂ) :
    (∑ a ∈ P, ∑ b ∈ S, (α a*β b*gauss (a*b))*
      heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀)) =
      (∑ e ∈ nearLogNormCells P S J A B X₀, logCellHeightSum P S α β J A B X₀ e h)+
      (∑ e ∈ farLogNormCells P S J A B X₀, logCellHeightSum P S α β J A B X₀ e h) := by
  rw [sum_near_farLogNormCells]
  let f := fun a b : Eisenstein => (α a*β b*gauss (a*b))*
    heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀)
  have hp := logNormCell_bilinear_partition P S J A B f
  calc
    _ = ∑ i ∈ P.image (logNormCell J A), ∑ j ∈ S.image (logNormCell J B),
        logCellHeightSum P S α β J A B X₀ (i,j) h := hp
    _ = _ := (Finset.sum_product (P.image (logNormCell J A)) (S.image (logNormCell J B))
      (fun e => logCellHeightSum P S α β J A B X₀ e h)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCellMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadic_logCell_left_mass (P S : Finset Eisenstein) {J A B : ℝ} (hJ : 1 ≤ J)
    (hP : ∀ a ∈ P, 1 ≤ norm a/A ∧ norm a/A ≤ 2)
    (hS : ∀ b ∈ S, 1 ≤ norm b/B ∧ norm b/B ≤ 2)
    (E : Finset (ℤ × ℤ))
    (hE : E ⊆ (P.image (logNormCell J A)).product (S.image (logNormCell J B)))
    (α : Eisenstein → ℂ) :
    (∑ e ∈ E, Real.sqrt (∑ a ∈ logNormCellSupport P J A e.1, ‖α a‖^2)) ≤
      4*J^2*Real.sqrt (∑ a ∈ P, ‖α a‖^2) := by
  let I := P.image (logNormCell J A)
  let L := S.image (logNormCell J B)
  let a := fun i => Real.sqrt (∑ n ∈ logNormCellSupport P J A i, ‖α n‖^2)
  have hi : (I.card:ℝ) ≤ 2*J := dyadic_logCell_card_bound P hJ hP
  have hl : (L.card:ℝ) ≤ 2*J := dyadic_logCell_card_bound S hJ hS
  have hs : (∑ i ∈ I, a i) ≤ Real.sqrt (I.card:ℝ)*Real.sqrt (∑ n ∈ P, ‖α n‖^2) := by
    have hh := cell_mass_sum_le I a
    simpa only [I,a,logNormCell_energy] using hh
  have hroot : Real.sqrt (I.card:ℝ) ≤ 2*J := by
    have hn := Real.sqrt_nonneg (I.card:ℝ)
    have hsq := Real.sq_sqrt (show 0 ≤ (I.card:ℝ) by positivity)
    nlinarith [sq_nonneg (Real.sqrt (I.card:ℝ)-1)]
  calc
    _ ≤ ∑ e ∈ I.product L, a e.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ => Real.sqrt_nonneg _)
    _ = (L.card:ℝ)*(∑ i ∈ I, a i) := by
      calc
        _ = ∑ i ∈ I, ∑ _j ∈ L, a i := Finset.sum_product I L _
        _ = _ := by
          simp only [Finset.sum_const,nsmul_eq_mul]
          rw [Finset.mul_sum]
    _ ≤ (2*J)*(Real.sqrt (I.card:ℝ)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)) :=
      mul_le_mul hl hs (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (by positivity)
    _ ≤ (2*J)*((2*J)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)) := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowFiniteProfile
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative family is selected independently of the requested
logarithmic saving. This order is needed for shrinking norm cutoffs. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

theorem low_variance_remainder_finite_seminorm
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ I : Finset (ℕ × ℕ), ∀ j : ℕ,
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
        (S : Finset Eisenstein) (β : Eisenstein → ℂ) (Z A T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t) V A-varianceZeroMode S β V A‖) T ≤
        K*(1+(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierSchwartz V hV hV'))*
          M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨I,D,hD,hprofile⟩ := exists_poissonProfileBudget_control
  refine ⟨I,?_⟩
  intro j
  obtain ⟨K,Ct,hK,hbound⟩ := ProfileControl.low_variance_remainder_height_log_saving
    hpnt j hMV hC hHuxley
  refine ⟨K*(1+D),Ct,by positivity,?_⟩
  intro V hV hV' S β Z A T M u hZ hA hT hM hS hβ
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hA0 : 0 ≤ A := (Real.rpow_nonneg (by linarith : 0 ≤ Z) _).trans hA
  obtain ⟨P,hPV,hP⟩ := hprofile V hV hV'
  have hb := hbound P S β Z A T M u hZ hA hT hM hS hβ
  rw [hPV] at hb
  let N := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
    (normProfileFourierSchwartz V hV hV')
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hc : K*P.cost ≤ K*(1+D)*(1+N) := by
    have hp : P.cost ≤ (1+D)*(1+N) := by nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hK.le
  apply hb.trans
  gcongr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowHeightSquareRoot
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace CubicFirstMoment

lemma height_mixed_square_root {f : ℝ → ℂ} (hf : Continuous f)
    {T K D E a b : ℝ} (hT : 0 < T) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ K*(D*b+E)*a) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤
      2*Real.sqrt K*(Real.sqrt D*Real.sqrt b+Real.sqrt E)*Real.sqrt a := by
  have hh := height_cell_square_root hf hT hK (mul_nonneg hD hb) hE ha
    (by norm_num : (0:ℝ) ≤ 1) (by simpa only [mul_one] using hsq)
  simpa only [Real.sqrt_one,mul_one,Real.sqrt_mul hD] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowShrinkingVariance
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The profile derivative loss is fixed before the logarithmic saving
is chosen. No height-dependent analytic hypothesis is introduced. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

theorem low_shrinking_variance_remainder
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (f : 𝓢(ℝ,ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    ∃ d : ℕ, ∀ j : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J c : ℝ) (hJ : 1 ≤ J), |c| ≤ 2 →
      ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ) (Z A T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t)
            (affineSchwartzProfile f J c (by linarith)) A-
          varianceZeroMode S β (affineSchwartzProfile f J c (by linarith)) A‖) T ≤
        K*J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨I,hfamily⟩ := low_variance_remainder_finite_seminorm hpnt hMV hC hHuxley
  obtain ⟨L,D,hD,hop⟩ := normProfileFourier_finite_seminorm I
  obtain ⟨d,E,hE,hshrink⟩ := affineSchwartzProfile_finite_cost f L
  refine ⟨d,?_⟩
  intro j
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily j
  refine ⟨K*(1+D*E),Ct,by positivity,?_⟩
  intro J c hJ hc S β Z A T M u hZ hA hT hM hS hβ
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hA0 : 0 ≤ A := (Real.rpow_nonneg (by linarith : 0 ≤ Z) _).trans hA
  let V := affineSchwartzProfile f J c (by linarith : J ≠ 0)
  have hVc := affineSchwartzProfile_compact f hf J c (by linarith)
  have hb := hbound V hVc (V.smooth ⊤) S β Z A T M u hZ hA hT hM hS hβ
  rw [←normProfileFourierCLM_apply V hVc] at hb
  have hcost := (hop V).trans (mul_le_mul_of_nonneg_left (hshrink J c hJ hc) hD.le)
  have hp : 1 ≤ J^d := one_le_pow₀ hJ
  have ht : K*(1+(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
      (normProfileFourierCLM V)) ≤ K*(1+D*E)*J^d := by
    apply (mul_le_mul_of_nonneg_left (show
        1+(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierCLM V) ≤ (1+D*E)*J^d from by nlinarith) hK.le).trans_eq
    ring
  apply hb.trans
  gcongr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowThinCell
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem low_thinCell_variance_height
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ j : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ) (_hJ : 1 ≤ J) (S : Finset Eisenstein)
        (β : Eisenstein → ℂ) (Z A T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t)
        (fun x => (thinCellCutoff J x : ℂ)) A‖) T ≤
        K*((A/J)*(∑ b ∈ S, ‖β b‖^2)+
          J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j) := by
  obtain ⟨d,hfamily⟩ := low_shrinking_variance_remainder hpnt hMV hC hHuxley
    thinBaseSchwartz thinBaseSchwartz_compact
  let D := 2*Real.pi/(9*Real.sqrt 3)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨d,?_⟩
  intro j
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily j
  refine ⟨K+2*D,Ct,by positivity,?_⟩
  intro J hJ S β Z A T M u hZ hA hT hM hS hβ
  have hJp : 0 < J := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hA
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos hL _).trans_le hT
  let V := fun x => (thinCellCutoff J x : ℂ)
  let Q := varianceZeroMode S β V A
  let R := fun t => smoothedDispersionVariance S β (u+t) V A-Q
  have hshift : |1+1/(2*J)| ≤ 2 := by
    rw [abs_of_pos (by positivity)]
    have hh : 1/(2*J) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hb := hbound J (1+1/(2*J)) hJ hshift S β Z A T M u hZ hA hT hM hS hβ
  rw [←thinCellCutoff_eq_affine J hJp.ne'] at hb
  have hz := thin_varianceZeroMode_bound S
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) β V hAp.le hJp
    (thinCellCutoff_norm J) (thinCellCutoff_support hJp)
  have hcont : Continuous (fun t => smoothedDispersionVariance S β (u+t) V A) :=
    (continuous_smoothedDispersionVariance S (fun b hb => (hS b hb).1) β V
      (thinCellCutoff_compact J hJp.ne') (thinCellCutoff_smooth J hJp.ne') hAp).comp
      (continuous_const.add continuous_id)
  have hRc : Continuous R := hcont.sub continuous_const
  have hm := dyadicHeightMean_mono hcont.norm (hRc.norm.add continuous_const) hTp
    (fun t _ => show ‖smoothedDispersionVariance S β (u+t) V A‖ ≤ ‖R t‖+‖Q‖ from
      norm_le_norm_sub_add _ _)
  change dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t) V A‖) T ≤
    dyadicHeightMean (fun t => ‖R t‖+‖Q‖) T at hm
  rw [dyadicHeightMean_add hRc.norm continuous_const,dyadicHeightMean_const _ hTp.ne'] at hm
  apply hm.trans
  have hmain := add_le_add hb (mul_le_mul_of_nonneg_left hz (by norm_num : (0:ℝ) ≤ 2))
  apply hmain.trans
  have hE : 0 ≤ ∑ b ∈ S, ‖β b‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hX : 0 ≤ J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j := by positivity
  have hAJ : 0 ≤ A/J := by positivity
  let E := (A/J)*(∑ b ∈ S, ‖β b‖^2)
  let X := J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j
  have hmissing : 0 ≤ K*E+2*D*X :=
    add_nonneg (mul_nonneg hK.le (mul_nonneg hAJ hE))
      (mul_nonneg (mul_nonneg (by norm_num) hD.le) hX)
  calc
    _ = K*X+2*D*E := by dsimp [X,E,D]; ring
    _ ≤ (K*X+2*D*E)+(K*E+2*D*X) := le_add_of_nonneg_right hmissing
    _ = _ := by dsimp [X,E]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowThinBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The thin diagonal keeps the actual coefficient energy, while only
the off-diagonal remainder uses the uniform coefficient bound. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem low_thinCell_bilinear_height_square
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ j : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 1 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1+1/(4*J) ≤ norm a/A ∧ norm a/A ≤ 1+3/(4*J)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖^2) T ≤
      K*((A/J)*(∑ b ∈ S, ‖β b‖^2)+
        J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j)*(∑ a ∈ P, ‖α a‖^2) := by
  obtain ⟨d,hfamily⟩ := low_thinCell_variance_height hpnt hMV hC hHuxley
  refine ⟨d,?_⟩
  intro j
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily j
  refine ⟨K,Ct,hK,?_⟩
  intro J hJ P S α β Z A T M u hZ hA hT hM hP hS hβ
  have hJp : 0 < J := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by nlinarith : 0 < Z) _).trans_le hA
  have hZ1 : 1 ≤ Z := by nlinarith
  have hTp : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ1]) _).trans_le hT
  have hb := height_bilinear_full_variance_bound_sq P S α β u
    (fun a ha => (hP a ha).1) (fun b hb => (hS b hb).1)
    (thinCellCutoff J) (thinCellCutoff_nonneg J)
    (thinCellCutoff_compact J hJp.ne') (thinCellCutoff_smooth J hJp.ne') hAp hTp
    (fun a ha => by rw [thinCellCutoff_one hJp (hP a ha).2])
  exact hb.trans ((mul_le_mul_of_nonneg_left
    (hbound J hJ S β Z A T M u hZ hA hT hM hS hβ)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowLogCellBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published-input dispersion bound on the actual disjoint log cells.
Restricting either finite coefficient sequence is performed explicitly. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem low_logCell_bilinear_height_square
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A B T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      ∀ i ∈ P.image (logNormCell J A), ∀ j : ℤ,
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ logNormCellSupport P J A i,
          ∑ b ∈ logNormCellSupport S J B j,
            α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖^2) T ≤
        K*((A/J)*(∑ b ∈ logNormCellSupport S J B j, ‖β b‖^2)+
          J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          (∑ a ∈ logNormCellSupport P J A i, ‖α a‖^2) := by
  obtain ⟨d,hfamily⟩ := low_thinCell_bilinear_height_square hpnt hMV hC hHuxley
  refine ⟨d,?_⟩
  intro q
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily q
  refine ⟨16*K,Ct,by positivity,?_⟩
  intro J hJ P S α β Z A B T M u hZ hA hT hM hP hS hβ i hi j
  have hJp : 0 < J := by linarith
  have hZp : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  obtain ⟨a,ha,hai⟩ := Finset.mem_image.mp hi
  have hai' : logNormCell J A a = i := hai
  have hscale := logCellScale_bounds hJ hAp (hP a ha).1 (hP a ha).2
  rw [hai'] at hscale
  have hAi : 0 < logCellScale J A i := logCellScale_pos hJp hAp i
  have hAiZ : Z^(3/2:ℝ) ≤ logCellScale J A i := by linarith [hscale.1]
  have hPa : ∀ a ∈ logNormCellSupport P J A i, primary a ∧
      1+1/(4*(J/8)) ≤ norm a/logCellScale J A i ∧
        norm a/logCellScale J A i ≤ 1+3/(4*(J/8)) := by
    intro a ha
    obtain ⟨ha,hai⟩ := Finset.mem_filter.mp ha
    refine ⟨(hP a ha).1,?_⟩
    have hb := log_cell_plateau (norm_pos_of_ne_zero (primary_ne_zero (hP a ha).1))
      hAp hJ (logNormCell J A a) (logNormCell_bounds J A a)
    rwa [hai] at hb
  have hSb : ∀ b ∈ logNormCellSupport S J B j,
      primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z :=
    fun b hb => hS b (Finset.mem_filter.mp hb).1
  have hh := hbound (J/8) (by linarith) (logNormCellSupport P J A i)
    (logNormCellSupport S J B j) α β Z (logCellScale J A i) T M u hZ hAiZ hT hM hPa hSb
    (fun b hb => hβ b (Finset.mem_filter.mp hb).1)
  have hm : logCellScale J A i/(J/8) ≤ 16*(A/J) := by
    calc
      _ ≤ (2*A)/(J/8) := div_le_div_of_nonneg_right hscale.2 (by positivity)
      _ = _ := by field_simp; ring
  have hp : (J/8)^d ≤ J^d := pow_le_pow_left₀ (by positivity) (by linarith) d
  have hpow : (logCellScale J A i)^(2/3:ℝ) ≤ 2*A^(2/3:ℝ) := by
    have ht : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (2/3:ℝ) ≤ 1)
    calc
      _ ≤ (2*A)^(2/3:ℝ) := Real.rpow_le_rpow hAi.le hscale.2 (by norm_num)
      _ = (2:ℝ)^(2/3:ℝ)*A^(2/3:ℝ) := Real.mul_rpow (by norm_num) hAp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (by positivity)
  have hrem : (J/8)^d*M^2*(logCellScale J A i)^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q ≤
      2*(J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q) := by
    have hm := mul_le_mul hp hpow (by positivity) (by positivity)
    have hm' := mul_le_mul_of_nonneg_right hm
      (show 0 ≤ M^2*Z^(5/3:ℝ)/(1+Real.log Z)^q by positivity)
    first | (convert hm' using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hm'.trans (le_of_eq (by ring)))
  let Eb := ∑ b ∈ logNormCellSupport S J B j, ‖β b‖^2
  have hEb : 0 ≤ Eb := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : (logCellScale J A i/(J/8))*Eb+
      (J/8)^d*M^2*(logCellScale J A i)^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q ≤
      16*((A/J)*Eb+J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q) := by
    have hm' := mul_le_mul_of_nonneg_right hm hEb
    nlinarith [show 0 ≤ J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q by positivity]
  apply hh.trans
  have he := mul_le_mul_of_nonneg_left hb hK.le
  have he' := mul_le_mul_of_nonneg_right he
    (Finset.sum_nonneg (fun a (_ : a ∈ logNormCellSupport P J A i) => sq_nonneg ‖α a‖))
  convert he' using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowNearHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The near-cell diagonal is summed with the degree-five incidence
bound. Only the logarithmically small remainder pays the cell-count cost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem low_near_logCell_height_bound
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖∑ e ∈ nearLogNormCells P S J A (Z/2) X₀,
        logCellPolynomial P S α β J A (Z/2) e (u+t)‖) T ≤
      K*(Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)+
        J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)) := by
  obtain ⟨d,hfamily⟩ := low_logCell_bilinear_height_square hpnt hMV hC hHuxley
  refine ⟨d,?_⟩
  intro q
  obtain ⟨K,Ct,hK,hcell⟩ := hfamily q
  refine ⟨10*Real.sqrt K,Ct,by positivity,?_⟩
  intro J hJ P S α β Z A X₀ T M u hZ hA hX hT hM hP hS hβ
  have hJ1 : 1 ≤ J := by linarith
  have hZp : 0 < Z := by nlinarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hTp : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ1]) _).trans_le hT
  let E := nearLogNormCells P S J A (Z/2) X₀
  let a := fun i => Real.sqrt (∑ n ∈ logNormCellSupport P J A i, ‖α n‖^2)
  let b := fun j => Real.sqrt (∑ n ∈ logNormCellSupport S J (Z/2) j, ‖β n‖^2)
  let R := J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q
  let H₁ := 2*Real.sqrt K*Real.sqrt (A/J)
  let H₂ := 2*Real.sqrt K*Real.sqrt R
  have hF (e : ℤ × ℤ) : Continuous
      (fun t : ℝ => logCellPolynomial P S α β J A (Z/2) e (u+t)) :=
    (logCellPolynomial_continuous P S α β J A (Z/2) e).comp
      (continuous_const.add continuous_id)
  have hh (e : ℤ × ℤ) (he : e ∈ E) :
      dyadicHeightMean (fun t => ‖logCellPolynomial P S α β J A (Z/2) e (u+t)‖) T ≤
        H₁*a e.1*b e.2+H₂*a e.1 := by
    have hi : e.1 ∈ P.image (logNormCell J A) :=
      (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
    have hb := height_mixed_square_root (hF e) hTp hK.le (by positivity)
      (show 0 ≤ R by dsimp [R]; positivity)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (hcell J hJ P S α β Z A (Z/2) T M u hZ hA hT hM hP hS hβ e.1 hi e.2)
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [H₁,H₂,a,b]
    ring
  have hs := dyadicHeightMean_norm_sum_le E
    (fun e t => logCellPolynomial P S α β J A (Z/2) e (u+t)) (fun e _ => hF e) hTp
  have hn := nearLogNormCells_energy_bound P S (fun a ha => (hP a ha).1)
    (fun b hb => (hS b hb).1) α β J hAp (by positivity : 0 < Z/2) hX
  have hl := dyadic_logCell_left_mass P S hJ1 (fun a ha => (hP a ha).2)
    (fun b hb => ⟨(le_div_iff₀ (by positivity : 0 < Z/2)).mpr (by simpa using (hS b hb).2.2.1),
      (div_le_iff₀ (by positivity : 0 < Z/2)).mpr (by nlinarith [(hS b hb).2.2.2])⟩)
    E (Finset.filter_subset _ _) α
  apply (hs.trans (Finset.sum_le_sum hh)).trans
  calc
    _ = H₁*(∑ e ∈ E, a e.1*b e.2)+H₂*(∑ e ∈ E, a e.1) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_assoc]
    _ ≤ H₁*(5*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2))+
        H₂*(4*J^2*Real.sqrt (∑ a ∈ P, ‖α a‖^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hn (by dsimp [H₁]; positivity))
        (mul_le_mul_of_nonneg_left hl (by dsimp [H₂]; positivity))
    _ ≤ _ := by
      dsimp [H₁,H₂,R]
      have hnon : 0 ≤ Real.sqrt K*J^2*
          Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2) := by positivity
      nlinarith only [hnon]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowNearIntegrated
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual near cells in the normalized, weighted height integral. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem low_near_logCell_integrated_bound
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M H : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ → (1+Real.log Z)^Ct ≤ T → 0 ≤ M → 0 ≤ H →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      ∀ h : ℝ → ℂ, Integrable h → (∀ t, ‖h t‖ ≤ H) →
      (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      ‖(T:ℂ)⁻¹*∑ e ∈ nearLogNormCells P S J A (Z/2) X₀,
        logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤
        K*H*(Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)+
          J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
            Real.sqrt (∑ a ∈ P, ‖α a‖^2)) := by
  obtain ⟨d,hfamily⟩ := low_near_logCell_height_bound hpnt hMV hC hHuxley
  refine ⟨d,?_⟩
  intro q
  obtain ⟨K,Ct,hK,hnear⟩ := hfamily q
  refine ⟨K,Ct,hK,?_⟩
  intro J hJ P S α β Z A X₀ T M H hZ hA hX hT hM hH hP hS hβ h hi hh hs
  have hZp : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos hL _).trans_le hT
  let E := nearLogNormCells P S J A (Z/2) X₀
  let f := fun t : ℝ => ∑ e ∈ E, logCellPolynomial P S α β J A (Z/2) e t
  let w := fun t : ℝ => h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)
  have hf : Continuous f := continuous_finsetSum E (fun e _ =>
    logCellPolynomial_continuous P S α β J A (Z/2) e)
  have hw : ∀ t, ‖w t‖ ≤ H := by
    intro t
    have hp : ‖Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)‖ = 1 := by simp [Complex.norm_exp]
    simpa only [w,norm_mul,hp,mul_one] using hh t
  have hws : ∀ t, t ∉ dyadicHeightSupport T → w t = 0 := by
    intro t ht
    simp only [w,hs t ht,zero_mul]
  have hb := normalized_dyadicWeightIntegral_bound f w hf hTp hH hw hws
  have hn := hnear J hJ P S α β Z A X₀ T M 0 hZ hA hX hT hM hP hS hβ
  simp only [zero_add] at hn
  rw [finite_logCellHeightSum_integral P S α β J A (Z/2) X₀ E h hi]
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left hn hH
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowLocalizedIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal height integral, with separate low-height diagonal and error.
The derivative degree is chosen before the desired logarithmic saving. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem low_localized_height_integral_bound_oai
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M H : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M → 0 ≤ H →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ H) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ H) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖(T:ℂ)⁻¹*(∑ a ∈ P, ∑ b ∈ S, (α a*β b*gauss (a*b))*
        heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀))‖ ≤
      K*(1+J*(J/T)^2)*H*(Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*
        Real.sqrt (∑ b ∈ S, ‖β b‖^2)+
        J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)) := by
  obtain ⟨dn,hnear⟩ := low_near_logCell_integrated_bound hpnt hMV hC hHuxley
  obtain ⟨df,hfar⟩ := low_far_logCell_integrated_bound hpnt hMV hC hHuxley
  refine ⟨dn+df,?_⟩
  intro q
  obtain ⟨Kn,Cn,hKn,hn⟩ := hnear q
  obtain ⟨Kf,Cf,hKf,hf⟩ := hfar q
  refine ⟨Kn+Kf,Cn+Cf,by positivity,?_⟩
  intro J hJ P S α β Z A X₀ T M H hZ hA hX hT hM hH hP hS hβ h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hJ1 : 1 ≤ J := by linarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hAp : 0 < A := lt_of_lt_of_le
    (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hL1 : 1 ≤ 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hTn : (1+Real.log Z)^Cn ≤ T :=
    (pow_le_pow_right₀ hL1 (by omega : Cn ≤ Cn+Cf)).trans hT
  have hTf : (1+Real.log Z)^Cf ≤ T :=
    (pow_le_pow_right₀ hL1 (by omega : Cf ≤ Cn+Cf)).trans hT
  let D := Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)
  let E := fun d : ℕ => J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
    Real.sqrt (∑ a ∈ P, ‖α a‖^2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE (d : ℕ) : 0 ≤ E d := by dsimp [E]; positivity
  have hmono (d : ℕ) (hd : d ≤ dn+df) : E d ≤ E (dn+df) := by
    dsimp [E]
    gcongr
  let Q := D+E (dn+df)
  have hQ : 0 ≤ Q := add_nonneg hD (hE _)
  have hn' : ‖(T:ℂ)⁻¹*∑ e ∈ nearLogNormCells P S J A (Z/2) X₀,
      logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤ Kn*H*Q := by
    have hb := hn J hJ P S α β Z A X₀ T M H hZ hA hX hTn hM hH hP hS hβ h hi hh hs
    apply hb.trans
    exact mul_le_mul_of_nonneg_left (add_le_add (le_refl D) (hmono dn (by omega)))
      (mul_nonneg hKn.le hH)
  have hf' : ‖(T:ℂ)⁻¹*∑ e ∈ farLogNormCells P S J A (Z/2) X₀,
      logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤ Kf*(J/T)^2*H*J*Q := by
    have hb := hf J hJ P S α β Z A X₀ T M H hZ hA hX hTf hM hH hP hS hβ
      h hi hd hi' hd' hi'' hh2 hs2
    apply hb.trans
    have he := (hmono df (by omega)).trans
      (le_mul_of_one_le_left (hE _) hJ1)
    have hb' := mul_le_mul_of_nonneg_left (add_le_add (le_refl (J*D)) he)
      (show 0 ≤ Kf*(J/T)^2*H by positivity)
    dsimp [D,E,Q] at hb' ⊢
    nlinarith only [hb']
  rw [logCellHeightSum_partition P S α β J A (Z/2) X₀ h,mul_add]
  apply (norm_add_le _ _).trans ((add_le_add hn' hf').trans ?_)
  have hx : 0 ≤ J*(J/T)^2 := by positivity
  have hb : Kn+Kf*(J*(J/T)^2) ≤ (Kn+Kf)*(1+J*(J/T)^2) := by
    nlinarith [mul_nonneg hKn.le hx]
  have hb' := mul_le_mul_of_nonneg_right hb (mul_nonneg hH hQ)
  dsimp [Q,D,E] at hb' ⊢
  nlinarith only [hb']

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.low_localized_height_integral_bound_oai := @OAI.CubicFirstMoment.low_localized_height_integral_bound_oai
