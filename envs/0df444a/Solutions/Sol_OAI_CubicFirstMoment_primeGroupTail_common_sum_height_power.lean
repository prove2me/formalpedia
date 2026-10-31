-- Prove2me | solution 1 for OAI.CubicFirstMoment.primeGroupTail_common_sum_height_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:45:08.726332+00:00
-- url     : https://prove2.me/submissions/1ef2038a-96d8-4011-8dc9-127eb76aa5b9

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A020
import Definitions.Def_OAIQ096A022
import Theorems.Thm_OAI_CubicFirstMoment_primeGroupTail_coprime_mellin_height_power

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_MixedPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary mixed characters and squarefree coset Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma traceFourier_affine (f : 𝓢(ℂ, ℂ)) (z q : ℂ) (hq : q ≠ 0) (w : ℂ) :
    traceFourier (fun x => f (z + q * x)) w =
      (Complex.normSq q)⁻¹ • ((Real.fourierChar (tracePair z (w/q)) : ℂ) *
        traceFourier f (w/q)) := by
  simpa only [traceFourier_translation] using
    (traceFourier_complexMul q hq (fun y => f (z+y)) w)

theorem poisson_eisenstein_periodic_coset (c : Eisenstein) (hc : c ≠ 0)
    (ψ : Residues c → ℂ) (f : 𝓢(ℂ, ℂ)) (z q : ℂ) (hq : q ≠ 0) :
    ∑' a : Eisenstein, ψ (Ideal.Quotient.mk (modulus c) a) * f (z+q*(a : ℂ)) =
      (2 / (Real.sqrt 3 * norm c * Complex.normSq q) : ℝ) • ∑' h : Eisenstein,
        (∑' v : Residues c, ψ v *
          (Real.fourierChar (tracePair (residueRepresentative c v : ℂ)
            ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ)) *
        (Real.fourierChar (tracePair z ((h : ℂ) / (q*(c : ℂ)*traceLambda))) : ℂ) *
        traceFourier f ((h : ℂ) / (q*(c : ℂ)*traceLambda)) := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexMulEquiv q hq)
    (f.compSubConstCLM ℂ (-z))
  have hg : (g : ℂ → ℂ) = (fun x => f (z+q*x)) := by
    funext x
    simp [g, add_comm]
  have he := poisson_eisenstein_periodic c hc ψ g
  rw [hg] at he
  simp_rw [traceFourier_affine f z q hq] at he
  have hfreq (h : Eisenstein) : ((h : ℂ) / ((c : ℂ)*traceLambda)) / q =
      (h : ℂ) / (q*(c : ℂ)*traceLambda) := by ring
  simp_rw [hfreq, mul_smul_comm, ← mul_assoc] at he
  rw [tsum_const_smul'', smul_smul] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end CubicFirstMoment

namespace CubicFirstMoment

theorem poisson_primary_mixed_squarefree {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (f : 𝓢(ℂ, ℂ)) :
    ∑' s : Eisenstein, mixedSymbol a b (a*b+3*s) * f ((a*b+3*s : Eisenstein) : ℂ) =
      (2 / (Real.sqrt 3 * norm (a*b) * 9) : ℝ) • ∑' h : Eisenstein,
        ((Real.sqrt (norm (a*b)) : ℂ) * (gauss a * star (gauss b)) *
          (star (cubicSymbol a h) * cubicSymbol b h)) *
        (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
        traceFourier f ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)) := by
  have hc0 := primary_ne_zero (primary_mul ha hb)
  have hc0' : ((a*b : Eisenstein) : ℂ) ≠ 0 := fun h => hc0 (Subtype.ext h)
  let ψ (v : Residues (a*b)) := mixedSymbol a b (3*residueRepresentative (a*b) v)
  have hψ (s : Eisenstein) : ψ (Ideal.Quotient.mk (modulus (a*b)) s) =
      mixedSymbol a b (a*b+3*s) := by
    apply mixedSymbol_congr
    simp only [map_mul, map_add, residueRepresentative_spec]
    have hz : Ideal.Quotient.mk (modulus (a*b)) (a*b) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton (a*b)))
    rw [map_mul] at hz
    rw [hz, zero_add]
  have hphase (h : Eisenstein) : tracePair ((a*b : Eisenstein) : ℂ)
      ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)) =
      tracePair (h : ℂ) (1 / (3*traceLambda)) := by
    unfold tracePair
    congr 2
    field_simp
  have hfin (h : Eisenstein) : (∑' v : Residues (a*b), ψ v *
      (Real.fourierChar (tracePair (residueRepresentative (a*b) v : ℂ)
        ((h : ℂ) / (((a*b : Eisenstein) : ℂ)*traceLambda))) : ℂ)) =
      (Real.sqrt (norm (a*b)) : ℂ) * (gauss a * star (gauss b)) *
        (star (cubicSymbol a h) * cubicSymbol b h) :=
    primaryMixedFourier_squarefree ha hb hsa hsb hab h
  have he := poisson_eisenstein_periodic_coset (a*b) hc0 ψ f
    ((a*b : Eisenstein) : ℂ) 3 (by norm_num)
  simp_rw [hψ, hfin, hphase] at he
  have h3 : ((3 : Eisenstein) : ℂ) = 3 := rfl
  norm_num [Subalgebra.coe_add, Subalgebra.coe_mul, Complex.normSq_ofNat, h3] at he ⊢
  exact he

end CubicFirstMoment
end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primaryCosetMap_bijective (c : Eisenstein) (hc : primary c) :
    Function.Bijective (primaryCosetMap c hc) := by
  constructor
  · intro s t hst
    have he : c+3*s=c+3*t := congrArg Subtype.val hst
    have hn : (3 : Eisenstein) ≠ 0 := by norm_num
    exact mul_left_cancel₀ hn (add_left_cancel he)
  · intro n
    obtain ⟨u, hu⟩ := n.property
    obtain ⟨v, hv⟩ := hc
    refine ⟨u-v, Subtype.ext ?_⟩
    change c+3*(u-v) = n.val
    linear_combination hv - hu

lemma tsum_primary_eq_coset (c : Eisenstein) (hc : primary c) (F : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if primary n then F n else 0) =
      ∑' s : Eisenstein, F (c+3*s) := by
  have he := (Equiv.ofBijective (primaryCosetMap c hc)
    (primaryCosetMap_bijective c hc)).tsum_eq (fun n => F n.val)
  change (∑' n : Eisenstein, Set.indicator {n | primary n} F n) = _
  rw [← tsum_subtype]
  exact he.symm

end CubicFirstMoment

namespace CubicFirstMoment

lemma traceFourier_normProfile (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) (w : ℂ) :
    traceFourier (normProfileSchwartz W hW hW' Z hZ) w =
      Z • traceFourier (fun z : ℂ => W (Complex.normSq z)) ((Real.sqrt Z : ℂ)*w) := by
  have hs : Real.sqrt Z ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hZ)
  have hs' : (Real.sqrt Z : ℂ) ≠ 0 := by exact_mod_cast hs
  have hn : Complex.normSq ((Real.sqrt Z : ℂ)⁻¹) = Z⁻¹ := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal, Real.mul_self_sqrt (le_of_lt hZ)]
  have hf : (normProfileSchwartz W hW hW' Z hZ : ℂ → ℂ) =
      fun z : ℂ => W (Complex.normSq ((Real.sqrt Z : ℂ)⁻¹*z)) := by
    funext z
    simp only [normProfileSchwartz_apply, Complex.normSq_mul, hn]
    congr 1
    ring
  rw [hf, traceFourier_complexMul _ (inv_ne_zero hs')
    (fun z => W (Complex.normSq z)) w, hn, inv_inv]
  congr 2
  simp only [div_inv_eq_mul, mul_comm]

theorem primaryCharacterGram_poisson {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) :
    primaryCharacterGram a b W Z =
      (2 / (Real.sqrt 3 * norm (a*b) * 9) : ℝ) • ∑' h : Eisenstein,
        ((Real.sqrt (norm (a*b)) : ℂ) * (gauss a * star (gauss b)) *
          (star (cubicSymbol a h) * cubicSymbol b h)) *
        (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
        (Z • traceFourier (fun z : ℂ => W (Complex.normSq z))
          ((Real.sqrt Z : ℂ) * ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)))) := by
  unfold primaryCharacterGram
  rw [tsum_primary_eq_coset (a*b) (primary_mul ha hb)
    (fun n => W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n))]
  have he := poisson_primary_mixed_squarefree ha hb hsa hsb hab
    (normProfileSchwartz W hW hW' Z hZ)
  simp_rw [traceFourier_normProfile W hW hW' hZ] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply tsum_congr
  intro s
  simp only [normProfileSchwartz_apply, mixedSymbol, norm]
  ring

end CubicFirstMoment

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

theorem primaryCharacterGram_poisson_normalized {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) :
    primaryCharacterGram a b W Z =
      ((Z / (9*Real.sqrt (norm (a*b))) : ℝ) : ℂ) * (gauss a * star (gauss b)) *
        ∑' h : Eisenstein, gramDualTerm a b W Z h := by
  have hN : 0 < norm (a*b) := Complex.normSq_pos.mpr
    (fun h => primary_ne_zero (primary_mul ha hb) (Subtype.ext h))
  have hsqrt : Real.sqrt (norm (a*b)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have hc : (2 / (Real.sqrt 3 * norm (a*b) * 9)) * Real.sqrt (norm (a*b)) * Z =
      (Z / (9*Real.sqrt (norm (a*b)))) * (2 / Real.sqrt 3) := by
    nth_rw 1 [← Real.sq_sqrt (le_of_lt hN)]
    field_simp
  have hc' := congrArg (fun x : ℝ => (x : ℂ)) hc
  push_cast at hc'
  rw [primaryCharacterGram_poisson ha hb hsa hsb hab W hW hW' hZ]
  simp only [Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro h
  simp only [gramDualTerm, normProfileFourier, Complex.real_smul]
  push_cast
  linear_combination (gauss a * star (gauss b) *
    (star (cubicSymbol a h) * cubicSymbol b h) *
    (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
    traceFourier (fun z : ℂ => W (Complex.normSq z))
      ((Real.sqrt Z : ℂ) * ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)))) * hc'

end CubicFirstMoment

namespace CubicFirstMoment

lemma normProfileFourier_mul_unit (W : ℝ → ℂ) {u : ℂ}
    (hu : Complex.normSq u = 1) (w : ℂ) :
    normProfileFourier W (u*w) = normProfileFourier W w := by
  have hu0 : u ≠ 0 := by
    intro he
    simp [he] at hu
  have hf : (fun z : ℂ => W (Complex.normSq (u⁻¹*z))) =
      (fun z : ℂ => W (Complex.normSq z)) := by
    funext z
    simp only [Complex.normSq_mul, Complex.normSq_inv, hu, inv_one, one_mul]
  have he := traceFourier_complexMul u⁻¹ (inv_ne_zero hu0)
    (fun z : ℂ => W (Complex.normSq z)) w
  rw [hf, Complex.normSq_inv, hu, inv_one, inv_one, one_smul] at he
  unfold normProfileFourier
  congr 1
  simpa only [div_inv_eq_mul, mul_comm] using he.symm

lemma normProfileFourier_eq_of_normSq_eq (W : ℝ → ℂ) {y y' : ℂ}
    (hy : Complex.normSq y = Complex.normSq y') :
    normProfileFourier W y = normProfileFourier W y' := by
  by_cases hy0 : y' = 0
  · have hy1 : y = 0 := Complex.normSq_eq_zero.mp (by simpa [hy0] using hy)
    rw [hy0, hy1]
  · have hu : Complex.normSq (y / y') = 1 := by
      rw [Complex.normSq_div, hy, div_self (mt Complex.normSq_eq_zero.mp hy0)]
    simpa only [div_mul_cancel₀ _ hy0] using normProfileFourier_mul_unit W hu y'

lemma normProfileFourier_radial (W : ℝ → ℂ) (y : ℂ) :
    normProfileFourier W y = radialDualProfile W (Complex.normSq y) := by
  apply normProfileFourier_eq_of_normSq_eq
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (Complex.normSq_nonneg y)]

lemma gramDualTerm_radial (a b : Eisenstein) (W : ℝ → ℂ) {Z : ℝ}
    (hZ : 0 ≤ Z) (h : Eisenstein) :
    gramDualTerm a b W Z h =
      (star (cubicSymbol a h) * cubicSymbol b h) *
        (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
          radialDualProfile W (Z * norm h / (27 * norm (a*b))) := by
  rw [gramDualTerm, normProfileFourier_radial]
  congr 2
  simp only [Complex.normSq_mul, Complex.normSq_div, Complex.normSq_ofReal,
    Real.mul_self_sqrt hZ, Complex.normSq_ofNat]
  have hl : Complex.normSq traceLambda = 3 := by
    rw [traceLambda_eq]
    simp [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt]
  rw [hl]
  dsimp [norm]
  ring

end CubicFirstMoment
end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealMoebius_sq (b : Eisenstein) :
    (idealMoebius b : ℝ)^2 = if Squarefree b then 1 else 0 := by
  unfold idealMoebius UniqueFactorizationMonoid.moebius
  split_ifs <;> push_cast
  · rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  · norm_num

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma mixedSymbol_remove_common {k a b : Eisenstein} (hk : primary k)
    (ha : primary a) (hb : primary b) (n : Eisenstein) :
    mixedSymbol (k*a) (k*b) n =
      if IsCoprime k n then mixedSymbol a b n else 0 := by
  rw [mixedSymbol, cubicSymbol_mul_lower (primary_ne_zero hk) (primary_ne_zero ha),
    cubicSymbol_mul_lower (primary_ne_zero hk) (primary_ne_zero hb), star_mul]
  by_cases hc : IsCoprime k n
  · rw [ite_eq_left hc]
    have hu : cubicSymbol k n * star (cubicSymbol k n) = 1 := by
      change cubicSymbol k n * starRingEnd ℂ (cubicSymbol k n) = 1
      rw [Complex.mul_conj', norm_cubicSymbol_of_isCoprime hk hc]
      norm_num
    simp only [mixedSymbol]
    linear_combination (cubicSymbol a n * star (cubicSymbol b n)) * hu
  · rw [ite_eq_right hc, cubicSymbol_eq_zero_of_not_isCoprime hk hc]
    simp

lemma primary_subsets_prod_dvd {k : Eisenstein} (hk : primary k)
    {s : Finset Eisenstein} (hs : s ⊆ primaryPrimeFactors k) (n : Eisenstein) :
    (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  constructor
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp) h
  · intro h
    apply Finset.prod_dvd_of_coprime _ h
    intro p hp q hq hpq
    exact primaryPrimes_isCoprime (primaryPrimeFactor_spec hk (hs hp)).1
      (primaryPrimeFactor_spec hk (hs hq)).1 hpq

theorem primary_moebius_coprimality {k : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (n : Eisenstein) :
    (if IsCoprime k n then (1 : ℂ) else 0) =
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℂ) *
          (if (∏ p ∈ s, p) ∣ n then 1 else 0) := by
  let P := primaryPrimeFactors k
  have hprod : (∏ p ∈ P, (1 - (if p ∣ n then (1 : ℂ) else 0))) =
      if IsCoprime k n then 1 else 0 := by
    by_cases h : IsCoprime k n
    · rw [ite_eq_left h]
      apply Finset.prod_eq_one
      intro p hp
      have hpn : ¬p ∣ n := by
        intro hd
        exact (primaryPrimeFactor_spec hk hp).1.2.not_isUnit
          (h.isUnit_of_dvd' (primaryPrimeFactor_spec hk hp).2 hd)
      simp [hpn]
    · rw [ite_eq_right h]
      have hex : ∃ p ∈ P, p ∣ n := by
        by_contra hn
        have hall : ∀ p ∈ P, IsCoprime p n := by
          intro p hp
          exact ((primaryPrimeFactor_spec hk hp).1.2.irreducible.coprime_iff_not_dvd).mpr
            (fun hd => hn ⟨p, hp, hd⟩)
        have := IsCoprime.prod_left hall
        rw [primaryPrimeFactors_prod hk hsk] at this
        exact h this
      obtain ⟨p, hp, hpn⟩ := hex
      apply Finset.prod_eq_zero hp
      simp [hpn]
  rw [← hprod]
  have hex := Finset.prod_add (fun p : Eisenstein => -(if p ∣ n then (1 : ℂ) else 0))
    (fun _ => (1 : ℂ)) P
  simp only [Finset.prod_const_one, mul_one, ← sub_eq_neg_add] at hex
  rw [hex]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub : s ⊆ primaryPrimeFactors k := Finset.mem_powerset.mp hs
  rw [idealMoebius_prod_primaryPrimes s
    (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).1), Finset.prod_neg]
  push_cast
  congr 1
  by_cases h : (∏ p ∈ s, p) ∣ n
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro p hp
    simp [(primary_subsets_prod_dvd hk hsub n).mp h p hp]
  · rw [ite_eq_right h]
    have hex : ∃ p ∈ s, ¬p ∣ n := by
      by_contra hn
      apply h
      apply (primary_subsets_prod_dvd hk hsub n).mpr
      intro p hp
      by_contra hpn
      exact hn ⟨p, hp, hpn⟩
    obtain ⟨p, hp, hpn⟩ := hex
    exact Finset.prod_eq_zero hp (by simp [hpn])

end CubicFirstMoment

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

lemma multiplesMap_bijective {m : Eisenstein} (hm : m ≠ 0) :
    Function.Bijective (multiplesMap m) := by
  constructor
  · intro x y h
    exact mul_left_cancel₀ hm (congrArg Subtype.val h)
  · intro n
    obtain ⟨x, hx⟩ := n.property
    exact ⟨x, Subtype.ext hx.symm⟩

lemma tsum_dvd_eq_multiples {m : Eisenstein} (hm : m ≠ 0) (F : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if m ∣ n then F n else 0) =
      ∑' x : Eisenstein, F (m*x) := by
  have he := (Equiv.ofBijective (multiplesMap m) (multiplesMap_bijective hm)).tsum_eq
    (fun n => F n.val)
  change (∑' n : Eisenstein, Set.indicator {n | m ∣ n} F n) = _
  rw [← tsum_subtype]
  exact he.symm

lemma tsum_primary_dvd_eq_multiples {m : Eisenstein} (hm : primary m)
    (F : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if primary n ∧ m ∣ n then F n else 0) =
      ∑' x : Eisenstein, if primary x then F (m*x) else 0 := by
  have he := tsum_dvd_eq_multiples (primary_ne_zero hm)
    (fun n => if primary n then F n else 0)
  convert he using 1
  · apply tsum_congr
    intro n
    by_cases hn : primary n <;> by_cases hd : m ∣ n <;> simp [hn, hd]
  · apply tsum_congr
    intro n
    have hp : primary (m*n) ↔ primary n := ⟨primary_of_mul hm, primary_mul hm⟩
    simp only [hp]

theorem primaryCharacterGram_divisor_scale {a b m : Eisenstein} (ha : primary a)
    (hb : primary b) (hm : primary m) (W : ℝ → ℂ) (Z : ℝ) :
    (∑' n : Eisenstein, if primary n ∧ m ∣ n then
      W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n) else 0) =
      mixedSymbol a b m * primaryCharacterGram a b W (Z / norm m) := by
  rw [tsum_primary_dvd_eq_multiples hm
    (fun n => W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n))]
  unfold primaryCharacterGram
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : primary n
  · have hnorm : norm (m*n) = norm m * norm n := Complex.normSq_mul _ _
    simp only [ite_eq_left hn, hnorm, div_div_eq_mul_div, cubicSymbol_mul_upper ha,
      cubicSymbol_mul_upper hb, star_mul, mixedSymbol]
    rw [show norm m * norm n / Z = norm n * norm m / Z by ring]
    ring
  · simp only [ite_eq_right hn, mul_zero]

theorem primaryCharacterGram_common_factor {k a b : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    primaryCharacterGram (k*a) (k*b) W Z =
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℂ) *
          mixedSymbol a b (∏ p ∈ s, p) *
            primaryCharacterGram a b W (Z / norm (∏ p ∈ s, p)) := by
  let P := (primaryPrimeFactors k).powerset
  let T (s : Finset Eisenstein) (n : Eisenstein) : ℂ :=
    (idealMoebius (∏ p ∈ s, p) : ℂ) *
      (if primary n ∧ (∏ p ∈ s, p) ∣ n then
        W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n) else 0)
  have hsumm (s : Finset Eisenstein) : Summable (T s) :=
    (summable_gram_restricted ha hb W hW hW' hZ (fun n => (∏ p ∈ s, p) ∣ n)).mul_left _
  have hpoint (n : Eisenstein) :
      (if primary n then W (norm n / Z) * cubicSymbol (k*a) n *
        star (cubicSymbol (k*b) n) else 0) = ∑ s ∈ P, T s n := by
    by_cases hn : primary n
    · simp only [ite_eq_left hn]
      rw [mul_assoc]
      change W (norm n / Z) * mixedSymbol (k*a) (k*b) n = _
      rw [mixedSymbol_remove_common hk ha hb]
      have he := primary_moebius_coprimality hk hsk n
      have hmul := congrArg (fun z : ℂ => z *
        (W (norm n / Z) * mixedSymbol a b n)) he
      simp only [Finset.sum_mul] at hmul
      convert hmul using 1
      · split_ifs <;> ring
      · apply Finset.sum_congr rfl
        intro s hs
        simp only [T, hn, true_and, mixedSymbol]
        split_ifs <;> ring
    · simp only [T, hn, false_and, ite_false, if_false, mul_zero, Finset.sum_const_zero]
  change (∑' n : Eisenstein, if primary n then _ else 0) = _
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun s _ => hsumm s)]
  apply Finset.sum_congr rfl
  intro s hs
  change (∑' n, (idealMoebius (∏ p ∈ s, p) : ℂ) * _) = _
  rw [tsum_mul_left]
  have hm : primary (∏ p ∈ s, p) := primary_finset_prod _ _
    (fun p hp => (primaryPrimeFactor_spec hk (Finset.mem_powerset.mp hs hp)).1.1)
  rw [primaryCharacterGram_divisor_scale ha hb hm]
  ring

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeDivisorWeight_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Eisenstein, primary a → Squarefree a →
      (2 : ℝ)^(primaryPrimeFactors a).card ≤ C * norm a ^ ε := by
  let R : ℝ := (2 : ℝ)^(1/ε)
  let U : Finset Eisenstein := (finite_norm_le R).toFinset
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hε.ne', Real.rpow_one]
  refine ⟨(2 : ℝ)^U.card, by positivity, ?_⟩
  intro a ha hsa
  let P := primaryPrimeFactors a
  have hpoint : ∀ p ∈ P, (2 : ℝ) ≤ (if p ∈ U then 2 else 1) * norm p ^ ε := by
    intro p hp
    have hn1 := one_le_norm (primaryPrimeFactor_spec ha hp).1.2.ne_zero
    by_cases hpU : p ∈ U
    · simp only [ite_eq_left hpU]
      nlinarith [Real.one_le_rpow hn1 hε.le]
    · simp only [ite_eq_right hpU, one_mul]
      have hRp : R ≤ norm p := le_of_lt (not_le.mp (by
        intro he
        exact hpU (by simpa [U] using he)))
      rw [← hRe]
      exact Real.rpow_le_rpow hR.le hRp hε.le
  have hprod := Finset.prod_le_prod (s := P) (fun _ _ => (by norm_num : (0 : ℝ) ≤ 2)) hpoint
  rw [Finset.prod_const, Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ P, if p ∈ U then (2 : ℝ) else 1) ≤ (2 : ℝ)^U.card := by
    rw [Finset.prod_ite_mem, Finset.prod_const]
    exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Finset.inter_subset_right))
  have heq : (∏ p ∈ P, norm p ^ ε) = norm a ^ ε := by
    rw [Real.finsetProd_rpow P norm (fun p _ => norm_nonneg p), ← norm_finset_prod]
    rw [primaryPrimeFactors_prod ha hsa]
  rw [heq] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (norm_nonneg a) _))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

open UniqueFactorizationMonoid
namespace CubicFirstMoment

lemma primeSet_subset_factors_of_prod_dvd {n : Eisenstein} (hn : primary n)
    {s : Finset Eisenstein} (hs : ∀ p ∈ s, primaryPrime p)
    (hd : (∏ p ∈ s, p) ∣ n) : s ⊆ primaryPrimeFactors n := by
  intro p hp
  exact primaryPrime_mem_factors hn (hs p hp)
    ((Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp).trans hd)

lemma primary_moebius_universal_indicator {U : Finset Eisenstein}
    (hU : ∀ p ∈ U, primaryPrime p) {a b : Eisenstein}
    (ha : primary a) (hsa : Squarefree a) (haU : primaryPrimeFactors a ⊆ U) :
    (if IsCoprime a b then (1 : ℂ) else 0) =
      ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p) : ℂ) *
        (if (∏ p ∈ s, p) ∣ a ∧ (∏ p ∈ s, p) ∣ b then (1 : ℂ) else 0) := by
  rw [primary_moebius_coprimality ha hsa]
  calc
    _ = ∑ s ∈ (primaryPrimeFactors a).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℂ) *
          (if (∏ p ∈ s, p) ∣ a ∧ (∏ p ∈ s, p) ∣ b then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hd : (∏ p ∈ s, p) ∣ a :=
        (primary_subsets_prod_dvd ha (Finset.mem_powerset.mp hs) a).mpr
          (fun p hp => (primaryPrimeFactor_spec ha (Finset.mem_powerset.mp hs hp)).2)
      simp only [hd, true_and]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr haU)
      intro s hs hn
      have hnd : ¬(∏ p ∈ s, p) ∣ a := by
        intro hd
        apply hn
        exact Finset.mem_powerset.mpr (primeSet_subset_factors_of_prod_dvd ha
          (fun p hp => hU p (Finset.mem_powerset.mp hs hp)) hd)
      simp [hnd]

theorem coprime_bilinear_moebius (S T U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U) (v w : Eisenstein → ℂ) :
    (∑ a ∈ S, ∑ b ∈ T, if IsCoprime a b then v a * star (w b) else 0) =
      ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p) : ℂ) *
        (∑ a ∈ S, if (∏ p ∈ s, p) ∣ a then v a else 0) *
          star (∑ b ∈ T, if (∏ p ∈ s, p) ∣ b then w b else 0) := by
  have hpoint (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) :
      (if IsCoprime a b then v a * star (w b) else 0) =
        ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p) : ℂ) *
          ((if (∏ p ∈ s, p) ∣ a then v a else 0) *
            star (if (∏ p ∈ s, p) ∣ b then w b else 0)) := by
    have hi := congrArg (fun z : ℂ => z * (v a * star (w b)))
      (primary_moebius_universal_indicator hU (hS a ha).1 (hS a ha).2 (hSU a ha)
        (b := b))
    rw [Finset.sum_mul] at hi
    convert hi using 1
    · split_ifs <;> simp
    · apply Finset.sum_congr rfl
      intro s hs
      split_ifs <;> simp_all
  simp_rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl
    (fun b _ => hpoint a ha b))]
  
  simp_rw [Finset.sum_comm (s := T) (t := U.powerset)]
  rw [Finset.sum_comm (s := S) (t := U.powerset)]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [star_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := T) (t := S)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end CubicFirstMoment

namespace CubicFirstMoment

lemma finiteCubicOperator_apply (S H : Finset Eisenstein) (u : Eisenstein → ℂ)
    (h : H) :
    finiteCubicOperator S H (WithLp.toLp 2 (fun a : S => u a.val)) h =
      ∑ a ∈ S, u a * cubicSymbol a h.val := by
  change (∑ a : S, cubicSymbol a.val h.val * u a.val) = _
  rw [← Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => cubicSymbol a h.val * u a)]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma finiteCubicBound_controls_mass (S H : Finset Eisenstein) (u : Eisenstein → ℂ) :
    (∑ h ∈ H, ‖∑ a ∈ S, u a * cubicSymbol a h‖^2) ≤
      finiteCubicBound S H * ∑ a ∈ S, ‖u a‖^2 := by
  let v : EuclideanSpace ℂ S := WithLp.toLp 2 (fun a : S => u a.val)
  have hb := (finiteCubicOperator S H).le_opNorm v
  have hs := pow_le_pow_left₀ (_root_.norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  change (∑ h : H, ‖finiteCubicOperator S H v h‖^2) ≤
      finiteCubicBound S H * ∑ a : S, ‖u a.val‖^2 at hs
  dsimp only [v] at hs
  simp_rw [finiteCubicOperator_apply] at hs
  simpa only [← Finset.sum_subtype H (fun _ => Iff.rfl)
    (fun h => ‖∑ a ∈ S, u a * cubicSymbol a h‖^2),
    ← Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => ‖u a‖^2)] using hs

end CubicFirstMoment

namespace CubicFirstMoment

theorem finiteCubicBound_bilinear (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1) :
    ‖∑ h ∈ H, phase h * (∑ a ∈ S, v a * cubicSymbol a h) *
      star (∑ a ∈ S, w a * cubicSymbol a h)‖ ≤
      finiteCubicBound S H *
        ((∑ a ∈ S, ‖v a‖^2) + (∑ a ∈ S, ‖w a‖^2)) / 2 := by
  let V (h : Eisenstein) := ∑ a ∈ S, v a * cubicSymbol a h
  let W (h : Eisenstein) := ∑ a ∈ S, w a * cubicSymbol a h
  calc
    _ ≤ ∑ h ∈ H, ‖phase h * V h * star (W h)‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ H, (‖V h‖^2+‖W h‖^2)/2 := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul, norm_mul, norm_star]
      calc
        _ ≤ 1 * ‖V h‖ * ‖W h‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hphase h hh) (_root_.norm_nonneg _))
            (_root_.norm_nonneg _)
        _ ≤ _ := by nlinarith [sq_nonneg (‖V h‖-‖W h‖)]
    _ = ((∑ h ∈ H, ‖V h‖^2) + (∑ h ∈ H, ‖W h‖^2))/2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by
      have hv := finiteCubicBound_controls_mass S H v
      have hw := finiteCubicBound_controls_mass S H w
      change (∑ h ∈ H, ‖V h‖^2) ≤ _ at hv
      change (∑ h ∈ H, ‖W h‖^2) ≤ _ at hw
      nlinarith

theorem finiteCubicBound_conjugate_bilinear (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1) :
    ‖∑ h ∈ H, phase h * (∑ a ∈ S, v a * star (cubicSymbol a h)) *
      star (∑ a ∈ S, w a * star (cubicSymbol a h))‖ ≤
      finiteCubicBound S H *
        ((∑ a ∈ S, ‖v a‖^2) + (∑ a ∈ S, ‖w a‖^2)) / 2 := by
  have h := finiteCubicBound_bilinear S H (fun a => star (w a))
    (fun a => star (v a)) phase hphase
  simp only [norm_star] at h
  have he : (∑ h ∈ H, phase h * (∑ a ∈ S, v a * star (cubicSymbol a h)) *
      star (∑ a ∈ S, w a * star (cubicSymbol a h))) =
      ∑ h ∈ H, phase h * (∑ a ∈ S, star (w a) * cubicSymbol a h) *
        star (∑ a ∈ S, star (v a) * cubicSymbol a h) := by
    apply Finset.sum_congr rfl
    intro h hh
    simp [star_sum, star_mul, mul_comm, mul_left_comm, mul_assoc]
  rw [he]
  simpa only [add_comm] using h

end CubicFirstMoment

namespace CubicFirstMoment

lemma norm_idealMoebius_le_one (m : Eisenstein) : ‖(idealMoebius m : ℂ)‖ ≤ 1 := by
  have hs : (idealMoebius m : ℝ)^2 ≤ 1 := by
    rw [idealMoebius_sq]
    split_ifs <;> norm_num
  have hn : ‖(idealMoebius m : ℂ)‖ = |(idealMoebius m : ℝ)| :=
    Complex.norm_intCast _
  rw [hn]
  nlinarith [sq_abs (idealMoebius m : ℝ), abs_nonneg (idealMoebius m : ℝ)]

theorem finiteCubicBound_coprime_bilinear (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1) :
    ‖∑ h ∈ H, phase h * ∑ a ∈ S, ∑ b ∈ S,
      if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0‖ ≤
      ∑ s ∈ U.powerset,
        finiteCubicBound (S.filter (fun a => (∏ p ∈ s, p) ∣ a)) H *
          ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) +
           (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖^2)) / 2 := by
  let V (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), v a * star (cubicSymbol a h)
  let W (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), w a * star (cubicSymbol a h)
  have he (h : Eisenstein) := coprime_bilinear_moebius S S U hS hU hSU
    (fun a => v a * star (cubicSymbol a h)) (fun a => w a * star (cubicSymbol a h))
  have he' (h : Eisenstein) :
      (∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0) =
      ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p) : ℂ) * V s h * star (W s h) := by
    simpa only [V, W, Finset.sum_filter] using he h
  simp_rw [he', Finset.mul_sum]
  rw [Finset.sum_comm]
  have hfactor (s : Finset Eisenstein) :
      (∑ h ∈ H, phase h * ((idealMoebius (∏ p ∈ s, p) : ℂ) * V s h * star (W s h))) =
      (idealMoebius (∏ p ∈ s, p) : ℂ) * ∑ h ∈ H, phase h * V s h * star (W s h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  simp_rw [hfactor]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∑ h ∈ H, phase h * V s h * star (W s h)‖ :=
      mul_le_mul_of_nonneg_right (norm_idealMoebius_le_one _) (_root_.norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact finiteCubicBound_conjugate_bilinear _ H v w phase hphase

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated radial Mellin kernels with uniform rapid decay. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem radialDualProfile_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      (1+t)^A * ‖radialDualProfile W t‖ ≤ C := by
  let F := normProfileFourierSchwartz W hW hW'
  let C := 2 ^ (2*A) * (Finset.Iic (2*A,0)).sup
      (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  have hC : 0 ≤ C := by positivity
  refine ⟨C+1, by linarith, ?_⟩
  intro t ht
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2*A,0)) (k := 2*A) (n := 0) (by rfl) (by rfl) F
      (Real.sqrt t : ℂ)
  simp only [norm_iteratedFDeriv_zero] at hb
  have hn : ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsmall : (1+t)^A ≤ (1+‖(Real.sqrt t : ℂ)‖)^(2*A) := by
    rw [hn, pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]
  have he : F (Real.sqrt t : ℂ) = radialDualProfile W t :=
    normProfileFourierSchwartz_apply W hW hW' _
  have hbound := mul_le_mul_of_nonneg_right hsmall (_root_.norm_nonneg (F (Real.sqrt t : ℂ)))
  rw [he] at hb hbound
  exact (hbound.trans hb).trans (by dsimp [C]; linarith)

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin integral bounds for coprime radial forms. -/

section

noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramMellinPhase_continuous (x : ℝ) : Continuous (fun t => gramMellinPhase t x) := by
  unfold gramMellinPhase
  fun_prop

lemma gramMellinPhase_mul (t : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    gramMellinPhase t (x*y) = gramMellinPhase t x * gramMellinPhase t y := by
  simp only [gramMellinPhase, Real.log_mul hx.ne' hy.ne', mul_add,
    AddChar.map_add_eq_mul, Circle.coe_mul]

lemma coprimeNormMajorant_phases (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) :
    coprimeNormMajorant S H U (fun a => v a * star (gramMellinPhase t (y a)))
      (fun a => w a * gramMellinPhase t (y a)) = coprimeNormMajorant S H U v w := by
  simp only [coprimeNormMajorant, norm_mul, norm_star, norm_gramMellinPhase, mul_one]

end CubicFirstMoment

namespace CubicFirstMoment

lemma coprimeMellinKernel_continuous (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (x y : Eisenstein → ℝ) :
    Continuous (coprimeMellinKernel S H v w phase x y) := by
  unfold coprimeMellinKernel
  apply continuous_finsetSum
  intro h hh
  apply Continuous.mul
  · exact continuous_const.mul (gramMellinPhase_continuous _)
  · apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    by_cases hab : IsCoprime a b
    · simp only [ite_eq_left hab]
      exact ((continuous_const.mul (gramMellinPhase_continuous _).star).mul
        continuous_const).mul
        (((continuous_const.mul (gramMellinPhase_continuous _)).mul continuous_const).star)
    · simp only [ite_eq_right hab]
      exact continuous_const

lemma norm_coprimeMellinKernel_le (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ) (t : ℝ) :
    ‖coprimeMellinKernel S H v w phase x y t‖ ≤ coprimeNormMajorant S H U v w := by
  have h := finiteCubicBound_coprime_bilinear S H U hS hU hSU
    (fun a => v a * star (gramMellinPhase t (y a)))
    (fun a => w a * gramMellinPhase t (y a))
    (fun h => phase h * gramMellinPhase t (x h)) (fun h hh => by
      simpa only [norm_mul, norm_gramMellinPhase, mul_one] using hphase h hh)
  change ‖coprimeMellinKernel S H v w phase x y t‖ ≤
    coprimeNormMajorant S H U _ _ at h
  rw [coprimeNormMajorant_phases] at h
  exact h

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency dyads and summable base Gram recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normNat_ne_zero_of_ne_zero {h : Eisenstein} (hh : h ≠ 0) : normNat h ≠ 0 := by
  intro hz
  apply hh
  apply norm_eq_zero_iff.mp
  rw [← normNat_cast,hz,Nat.cast_zero]

lemma mem_frequencyDyad {j : ℕ} {h : Eisenstein} :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.log 2 (normNat h) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_nonzeroNormBall]
  refine ⟨fun h => ⟨h.1.2,h.2⟩,fun hh => ⟨⟨?_,hh.1⟩,hh.2⟩⟩
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at ht
  rw [← normNat_cast]
  exact_mod_cast ht.le

lemma frequencyDyad_norm {j : ℕ} {h : Eisenstein} (hh : h ∈ frequencyDyad j) :
    (2 : ℝ)^j ≤ norm h ∧ norm h ≤ 2*(2 : ℝ)^j := by
  rw [mem_frequencyDyad] at hh
  have hl := Nat.pow_log_le_self 2 (normNat_ne_zero_of_ne_zero hh.1)
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at hl ht
  rw [← normNat_cast]
  constructor
  · exact_mod_cast hl
  · have ht' : (normNat h : ℝ) ≤ (2 : ℝ)^(j+1) := by exact_mod_cast ht.le
    simpa [pow_succ,mul_comm] using ht'

lemma summable_gramDualTerm {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) : Summable (gramDualTerm a b W Z) := by
  let q : ℂ := (Real.sqrt Z : ℂ)/(3*((a*b : Eisenstein) : ℂ)*traceLambda)
  have hq : q ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hZ)
    · exact mul_ne_zero (mul_ne_zero (by norm_num)
        (fun hz => mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb) (Subtype.ext hz)))
        traceLambda_ne_zero
  have hs := (schwartz_summable_eisenstein_coset
    (normProfileFourierSchwartz W hW hW') q hq 0).norm
  apply Summable.of_norm_bounded hs
  intro h
  rw [zero_add,normProfileFourierSchwartz_apply]
  dsimp only [q]
  have he : ((Real.sqrt Z : ℂ)/(3*((a*b : Eisenstein) : ℂ)*traceLambda))*(h : ℂ) =
      (Real.sqrt Z : ℂ)*((h : ℂ)/(3*((a*b : Eisenstein) : ℂ)*traceLambda)) := by ring
  rw [he]
  simp only [gramDualTerm,norm_mul,norm_star,Circle.norm_coe,mul_one]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  exact (mul_le_mul (norm_cubicSymbol_le_one ha h) (norm_cubicSymbol_le_one hb h)
    (_root_.norm_nonneg _) (by norm_num)).trans (by norm_num)

lemma hasSum_frequencyDyad (F : Eisenstein → ℂ) (hF : Summable F) (h0 : F 0 = 0) :
    HasSum (fun j : ℕ => ∑ h ∈ frequencyDyad j, F h) (∑' h : Eisenstein, F h) := by
  have he := hF.hasSum.tsum_fiberwise (fun h : Eisenstein => Nat.log 2 (normNat h))
  have hf (j : ℕ) : (∑' h : ((fun h : Eisenstein => Nat.log 2 (normNat h)) ⁻¹' {j}), F h) =
      ∑ h ∈ frequencyDyad j, F h := by
    rw [tsum_subtype]
    calc
      _ = ∑ h ∈ frequencyDyad j,
          Set.indicator ((fun h : Eisenstein => Nat.log 2 (normNat h)) ⁻¹' {j}) F h := by
        apply tsum_eq_sum
        intro h hh
        by_cases hz : h = 0
        · subst h; simp [h0]
        · have hj : Nat.log 2 (normNat h) ≠ j := fun hj => hh (mem_frequencyDyad.mpr ⟨hz,hj⟩)
          simp [hj]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h hh
        have hm : h ∈ ((fun h : Eisenstein => Nat.log 2 (normNat h)) ⁻¹' {j}) :=
          (mem_frequencyDyad.mp hh).2
        exact Set.indicator_of_mem hm F

  simpa only [hf] using he

end CubicFirstMoment

namespace CubicFirstMoment

lemma frequencyDyad_card_le (j : ℕ) :
    ((frequencyDyad j).card : ℝ) ≤ 36*(2 : ℝ)^j := by
  have hs : frequencyDyad j ⊆ nonzeroNormBall ((2 : ℝ)^(j+1)) := Finset.filter_subset _ _
  have hh : ((frequencyDyad j).card : ℝ) ≤ (nonzeroNormBall ((2 : ℝ)^(j+1))).card := by
    exact_mod_cast Finset.card_le_card hs
  exact hh.trans ((nonzeroNormBall_card_le (by positivity)).trans_eq (by rw [pow_succ]; ring))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma commonBlockCoefficient_norm_le (u : Eisenstein → ℂ) (k m : Eisenstein)
    {a : Eisenstein} (ha : primary a) :
    ‖commonBlockCoefficient u k m a‖ ≤ ‖u (k*a)‖ := by
  unfold commonBlockCoefficient
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left (norm_cubicSymbol_le_one ha m) (_root_.norm_nonneg _)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramified residual factors and full cube decomposition. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_le_of_dvd {a b : Eisenstein} (hb : b ≠ 0) (hd : a ∣ b) :
    norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := hd
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg a) (one_le_norm hc)

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GlobalRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summed dual norms and full smoothed sieve recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma commonBlockEnergy_nonneg (S : Finset Eisenstein) (u : Eisenstein → ℂ) (k : Eisenstein) :
    0 ≤ commonBlockEnergy S u k := Finset.sum_nonneg (fun a _ => by positivity)

lemma commonBlockCoefficient_energy_le (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    {k : Eisenstein} (hk : primary k) (m : Eisenstein) :
    (∑ a ∈ residualRows S k, (2 : ℝ)^(primaryPrimeFactors a).card *
      ‖commonBlockCoefficient u k m a‖^2) ≤ commonBlockEnergy S u k := by
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (commonBlockCoefficient_norm_le u k m (residualRows_primary hk hS a ha).1) 2

lemma commonBlockCoefficient_unweighted_energy_le (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    {k : Eisenstein} (hk : primary k) (m : Eisenstein) :
    (∑ a ∈ residualRows S k, ‖commonBlockCoefficient u k m a‖^2) ≤ commonBlockEnergy S u k := by
  apply le_trans _ (commonBlockCoefficient_energy_le S hS u hk m)
  apply Finset.sum_le_sum
  intro a ha
  exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (by norm_num))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact sieve majorants and common-factor energy bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_subset_of_dvd {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hab : a ∣ b) : primaryPrimeFactors a ⊆ primaryPrimeFactors b := by
  intro p hp
  obtain ⟨hpp,hpa⟩ := primaryPrimeFactor_spec ha hp
  exact primaryPrime_mem_factors hb hpp (hpa.trans hab)

lemma primary_divisors_card_le (T : Finset Eisenstein)
    (hT : ∀ k ∈ T, primary k ∧ Squarefree k) {p : Eisenstein} (hp : primary p) :
    ((T.filter (· ∣ p)).card : ℝ) ≤ (2 : ℝ)^(primaryPrimeFactors p).card := by
  have hmaps : ∀ k ∈ T.filter (· ∣ p), primaryPrimeFactors k ∈ (primaryPrimeFactors p).powerset := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact Finset.mem_powerset.mpr (primaryPrimeFactors_subset_of_dvd (hT k hk.1).1 hp hk.2)
  have hinj : Set.InjOn primaryPrimeFactors (↑(T.filter (· ∣ p)) : Set Eisenstein) := by
    intro k hk l hl he
    have hk' := hT k (Finset.mem_filter.mp hk).1
    have hl' := hT l (Finset.mem_filter.mp hl).1
    rw [← primaryPrimeFactors_prod hk'.1 hk'.2,← primaryPrimeFactors_prod hl'.1 hl'.2,he]
  have hc := (Finset.card_image_iff.mpr hinj).symm.le.trans
    (Finset.card_le_card (Finset.image_subset_iff.mpr hmaps))
  rw [Finset.card_powerset] at hc
  exact_mod_cast hc

lemma residualRows_sum_image (S : Finset Eisenstein) {k : Eisenstein} (hk : k ≠ 0)
    (f : Eisenstein → ℝ) :
    (∑ a ∈ residualRows S k, f (k*a)) = ∑ p ∈ S, if k ∣ p then f p else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => k*a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨(mem_residualRows hk).mp ha, dvd_mul_right _ _⟩
  · intro a ha b hb hab
    exact mul_left_cancel₀ hk hab
  · intro p hp
    obtain ⟨a,rfl⟩ := (Finset.mem_filter.mp hp).2
    exact ⟨a,(mem_residualRows hk).mpr (Finset.mem_filter.mp hp).1,rfl⟩
  · intro a ha
    rfl

lemma common_energy_cubic_weight (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ) :
    (∑ k ∈ commonRowFactors S, (2 : ℝ)^(primaryPrimeFactors k).card *
      commonBlockEnergy S u k) ≤
      ∑ p ∈ S, ((2 : ℝ)^(primaryPrimeFactors p).card)^3 * ‖u p‖^2 := by
  have hT (k : Eisenstein) (hk : k ∈ commonRowFactors S) := commonRowFactors_spec hS hk
  have hw (k : Eisenstein) (hk : k ∈ commonRowFactors S) :
      (2 : ℝ)^(primaryPrimeFactors k).card * commonBlockEnergy S u k ≤
        ∑ p ∈ S, if k ∣ p then ((2 : ℝ)^(primaryPrimeFactors p).card)^2 * ‖u p‖^2 else 0 := by
    rw [← residualRows_sum_image S (primary_ne_zero (hT k hk).1)]
    unfold commonBlockEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hpS := (mem_residualRows (primary_ne_zero (hT k hk).1)).mp ha
    have hp := (hS (k*a) hpS).1
    have haa := (residualRows_primary (hT k hk).1 hS a ha).1
    have hka : (2 : ℝ)^(primaryPrimeFactors k).card ≤ (2 : ℝ)^(primaryPrimeFactors (k*a)).card :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_card
        (primaryPrimeFactors_subset_of_dvd (hT k hk).1 hp (dvd_mul_right _ _)))
    have haa' : (2 : ℝ)^(primaryPrimeFactors a).card ≤ (2 : ℝ)^(primaryPrimeFactors (k*a)).card :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_card
        (primaryPrimeFactors_subset_of_dvd haa hp (dvd_mul_left _ _)))
    calc
      _ = ((2 : ℝ)^(primaryPrimeFactors k).card*(2 : ℝ)^(primaryPrimeFactors a).card)*‖u (k*a)‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul hka haa' (by positivity) (by positivity)]) (sq_nonneg _)
  calc
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ p ∈ S,
        if k ∣ p then ((2 : ℝ)^(primaryPrimeFactors p).card)^2 * ‖u p‖^2 else 0 :=
      Finset.sum_le_sum hw
    _ = ∑ p ∈ S, ((commonRowFactors S).filter (· ∣ p)).card *
        (((2 : ℝ)^(primaryPrimeFactors p).card)^2 * ‖u p‖^2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hc := primary_divisors_card_le (commonRowFactors S)
        (fun k hk => ⟨(hT k hk).1,(hT k hk).2⟩) (hS p hp).1
      calc
        _ ≤ (2 : ℝ)^(primaryPrimeFactors p).card *
            (((2 : ℝ)^(primaryPrimeFactors p).card)^2 * ‖u p‖^2) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring

theorem common_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (X : ℝ),
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ X) →
      (∑ k ∈ commonRowFactors S, (2 : ℝ)^(primaryPrimeFactors k).card *
        commonBlockEnergy S u k) ≤ C * X^ε * ∑ a ∈ S, ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := primeDivisorWeight_small_power (ε/3) (by positivity)
  refine ⟨C^3,by positivity,?_⟩
  intro S u X hS
  apply (common_energy_cubic_weight S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) u).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h := pow_le_pow_left₀ (by positivity) (hbound a (hS a ha).1 (hS a ha).2.1) 3
  have he : (norm a ^ (ε/3))^3 = norm a ^ ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg a)]
    congr 1
    norm_num
  rw [mul_pow,he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg a) (hS a ha).2.2 hε.le) (by positivity))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- The squarefree weight equals the squared absolute value of the normalized
Gauss sum, for primary elements. -/
theorem gauss_mul_star_squarefree {a : Eisenstein} (ha : primary a) :
    gauss a * star (gauss a) = if Squarefree a then (1 : ℂ) else 0 := by
  have hnorm := Complex.mul_conj' (gauss a)
  simp only [starRingEnd_apply] at hnorm
  rw [hnorm, norm_gauss ha]
  split_ifs <;> norm_num

theorem norm_gauss_le_one {a : Eisenstein} (ha : primary a) : ‖gauss a‖ ≤ 1 := by
  rw [norm_gauss ha]
  split_ifs <;> norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- For a coprime pair, the normalized Gauss factors cancel against those
in the lattice Poisson formula, leaving the explicit character frequency sum. -/
theorem dispersion_pair_poisson {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q)
    (hpq : IsCoprime p q) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    dispersionAmplitude β u p * star (dispersionAmplitude β u q) *
      primaryCharacterGram q p W A =
      β p * star (β q) * normTwist u p * star (normTwist u q) *
        ((A / (9 * Real.sqrt (norm (q*p))) : ℝ) : ℂ) *
          ∑' h : Eisenstein, gramDualTerm q p W A h := by
  rw [primaryCharacterGram_poisson_normalized hq hp hsq hsp hpq.symm W hW hW' hA]
  have hg₁ : gauss p * star (gauss p) = 1 := by
    simpa only [ite_eq_left hsp] using gauss_mul_star_squarefree hp
  have hg₂ : gauss q * star (gauss q) = 1 := by
    simpa only [ite_eq_left hsq] using gauss_mul_star_squarefree hq
  simp only [dispersionAmplitude, star_mul]
  calc
    _ = (β p * star (β q) * normTwist u p * star (normTwist u q) *
          ((A / (9 * Real.sqrt (norm (q*p))) : ℝ) : ℂ) *
            ∑' h : Eisenstein, gramDualTerm q p W A h) *
          (gauss p * star (gauss p)) * (gauss q * star (gauss q)) := by ring
    _ = _ := by rw [hg₁, hg₂, mul_one, mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth weights and Mellin twists

The derivative cost below explains why the unweighted published Hecke
estimate continues to give any prescribed logarithmic saving after a
fixed-logarithmic-height norm twist. It is used with `weighted_cubic_prime_bound`.
-/

noncomputable section

namespace CubicFirstMoment

theorem normTwist_eq_mellinPhase (u : ℝ) (a : Eisenstein) :
    normTwist u a = mellinPhase u (norm a) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeMellinMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The divisor expansion of the actual radial kernel is bounded by its
literal character-row masses. This keeps the oscillation that is lost in
the coarse operator norm bound. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finite_bilinear_mass_bound {α : Type*} (H : Finset α)
    (v w phase : α → ℂ) (hp : ∀ h ∈ H, ‖phase h‖ ≤ 1) :
    ‖∑ h ∈ H, phase h*v h*star (w h)‖ ≤
      ((∑ h ∈ H, ‖v h‖^2)+(∑ h ∈ H, ‖w h‖^2))/2 := by
  apply (norm_sum_le _ _).trans
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro h hh
  rw [norm_mul,norm_mul,norm_star]
  calc
    _ ≤ ‖v h‖*‖w h‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (_root_.norm_nonneg _) (hp h hh)) (_root_.norm_nonneg _)
    _ ≤ _ := by nlinarith [sq_nonneg (‖v h‖-‖w h‖)]

theorem norm_coprimeMellinKernel_le_mass (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ) (t : ℝ) :
    ‖coprimeMellinKernel S H v w phase x y t‖ ≤ coprimeMellinMass S H U v w y t := by
  let V (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h)
  let W (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      w a*gramMellinPhase t (y a)*star (cubicSymbol a h)
  have he (h : Eisenstein) := coprime_bilinear_moebius S S U hS hU hSU
    (fun a => v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h))
    (fun a => w a*gramMellinPhase t (y a)*star (cubicSymbol a h))
  have he' (h : Eisenstein) :
      (∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
        (v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h))*
          star (w b*gramMellinPhase t (y b)*star (cubicSymbol b h)) else 0) =
      ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p):ℂ)*V s h*star (W s h) := by
    simpa only [V,W,Finset.sum_filter] using he h
  unfold coprimeMellinKernel
  simp_rw [he',Finset.mul_sum]
  rw [Finset.sum_comm]
  have hf (s : Finset Eisenstein) :
      (∑ h ∈ H, (phase h*gramMellinPhase t (x h))*
        ((idealMoebius (∏ p ∈ s, p):ℂ)*V s h*star (W s h))) =
      (idealMoebius (∏ p ∈ s, p):ℂ)*
        ∑ h ∈ H, (phase h*gramMellinPhase t (x h))*V s h*star (W s h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  simp_rw [hf]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [norm_mul]
  apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
  exact finite_bilinear_mass_bound H (V s) (W s)
    (fun h => phase h*gramMellinPhase t (x h)) (fun h hh => by
      simpa only [norm_mul,norm_gramMellinPhase,mul_one] using hphase h hh)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeMellinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integral estimate for the literal radial Poisson form in terms of
the actual divisor-restricted character moments. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellin_character_row_norm_le (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (v : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (h : Eisenstein) (t : ℝ) :
    ‖∑ a ∈ S, v a*gramMellinPhase t (y a)*star (cubicSymbol a h)‖ ≤
      ∑ a ∈ S, ‖v a‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul,norm_mul,norm_gramMellinPhase,mul_one,norm_star]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS a ha) _)

lemma coprimeMellinMass_nonneg (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) : 0 ≤ coprimeMellinMass S H U v w y t := by
  apply Finset.sum_nonneg
  intro s hs
  exact div_nonneg (add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by norm_num)

lemma coprimeMellinMass_continuous (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) : Continuous (coprimeMellinMass S H U v w y) := by
  unfold coprimeMellinMass
  apply continuous_finsetSum
  intro s hs
  apply Continuous.div_const
  apply Continuous.add
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact (continuous_const.mul (gramMellinPhase_continuous _).star).mul continuous_const
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact (continuous_const.mul (gramMellinPhase_continuous _)).mul continuous_const

lemma coprimeMellinMass_le_envelope (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) :
    coprimeMellinMass S H U v w y t ≤
      ∑ s ∈ U.powerset, (H.card:ℝ)*
        ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖)^2+
         (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖)^2)/2 := by
  unfold coprimeMellinMass
  apply Finset.sum_le_sum
  intro s hs
  let F := S.filter (fun a => (∏ p ∈ s, p) ∣ a)
  have hF : ∀ a ∈ F, primary a := fun a ha => hS a (Finset.mem_filter.mp ha).1
  have hneg (h : Eisenstein) :
      ‖∑ a ∈ F, v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h)‖ ≤
      ∑ a ∈ F, ‖v a‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a ha
    rw [norm_mul,norm_mul,norm_star,norm_gramMellinPhase,mul_one,norm_star]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hF a ha) _)
  have hv := Finset.sum_le_sum (s := H) (fun h _ =>
    pow_le_pow_left₀ (_root_.norm_nonneg _) (hneg h) 2)
  have hw := Finset.sum_le_sum (s := H) (fun h _ =>
    pow_le_pow_left₀ (_root_.norm_nonneg _) (mellin_character_row_norm_le F hF w y h t) 2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hv hw
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (add_le_add hv hw).trans_eq (by dsimp [F]; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramMellin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation on the entire fixed norm range of a prime
convolution. The cutoff belongs to the transform, so no cutoff is inserted
into the arithmetic coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma wideGramLogKernel_eq_radial (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    {ρ u : ℝ} (hρ : 0 ≤ ρ) (hu : |u| ≤ M) :
    wideGramLogKernel M hM W ρ u = radialDualProfile W (ρ*Real.exp u) := by
  have hcut : wideGramLogBump M hM u = 1 :=
    (wideGramLogBump M hM).one_of_mem_closedBall
      (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,wideGramLogBump] using hu)
  rw [wideGramLogKernel,hcut,one_smul,normProfileFourier_radial]
  congr 1
  rw [Complex.normSq_ofReal]
  calc
    _ = (Real.sqrt ρ*Real.sqrt ρ)*(Real.exp (u/2)*Real.exp (u/2)) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hρ,← Real.exp_add]; congr 2; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeNormRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed log-norm range for an unchanged prime convolution is derived
from its coordinate supports. -/
noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma compact_norm_log_ratio {D x y z : ℝ} (_hD : 1 ≤ D)
    (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) D) (hz : z ∈ Icc (1:ℝ) D) :
    |Real.log x-Real.log (y*z)| ≤ 1+2*Real.log D := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hy0 : 0 < y := zero_lt_one.trans_le hy.1
  have hz0 : 0 < z := zero_lt_one.trans_le hz.1
  have hxlog : Real.log x ≤ 1 :=
    (Real.log_le_sub_one_of_pos hx0).trans (by linarith [hx.2])
  have hylog : Real.log y ≤ Real.log D := Real.log_le_log hy0 hy.2
  have hzlog : Real.log z ≤ Real.log D := Real.log_le_log hz0 hz.2
  rw [Real.log_mul hy0.ne' hz0.ne',abs_le]
  constructor <;> linarith [Real.log_nonneg hx.1,Real.log_nonneg hy.1,
    Real.log_nonneg hz.1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormDenominatorMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma normDenominatorMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (normDenominatorMellinCoefficient M hM W hW hW' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integrable

lemma normDenominatorLogSchwartz_apply (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ u : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ u =
      (Real.exp (u/2):ℂ)*wideGramLogKernel M hM W ρ u := by
  rw [normDenominatorLogSchwartz,SchwartzMap.smulLeftCLM_apply_apply
    (normDenominatorMultiplier M hM).hasTemperateGrowth,wideGramLogSchwartz_apply]
  change ((wideGramLogBump (2*M) (by positivity) u:ℝ) • (Real.exp (u/2):ℂ)) •
    wideGramLogKernel M hM W ρ u = _
  by_cases hu : |u| ≤ 2*M
  · have he : wideGramLogBump (2*M) (by positivity) u = 1 :=
      (wideGramLogBump (2*M) (by positivity)).one_of_mem_closedBall
        (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,wideGramLogBump] using hu)
    rw [he,one_smul,smul_eq_mul]
  · have he : wideGramLogBump M hM u = 0 :=
      (wideGramLogBump M hM).zero_of_le_dist
        (by simpa only [Real.dist_eq,sub_zero,wideGramLogBump] using le_of_not_ge hu)
    simp only [wideGramLogKernel,he,zero_smul,smul_zero,mul_zero]

lemma normDenominatorLogSchwartz_eq_radial (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ u : ℝ} (hρ : 0 ≤ ρ) (hu : |u| ≤ M) :
    normDenominatorLogSchwartz M hM W hW hW' ρ u =
      (Real.exp (u/2):ℂ)*radialDualProfile W (ρ*Real.exp u) := by
  rw [normDenominatorLogSchwartz_apply,wideGramLogKernel_eq_radial M hM W hρ hu]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormDenominatorSeparation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the square-root norm denominator in Poisson summation. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

theorem normDenominator_radial_mellin_separated (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ}
    (hρ : 0 ≤ ρ) (hx : 0 < x) (hy : 0 < y) (hxy : |Real.log x-Real.log y| ≤ M) :
    (Real.exp ((Real.log x-Real.log y)/2):ℂ)*radialDualProfile W (ρ*x/y) = ∫ t : ℝ,
      normDenominatorMellinCoefficient M hM W hW hW' ρ t*gramMellinPhase t x*star (gramMellinPhase t y) := by
  have hk := normDenominatorLogSchwartz_eq_radial M hM W hW hW' hρ hxy
  rw [Real.exp_sub,Real.exp_log hx,Real.exp_log hy,← mul_div_assoc] at hk
  rw [← hk]
  have he := congrArg (fun f : 𝓢(ℝ,ℂ) => f (Real.log x-Real.log y))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ,ℂ))
      (normDenominatorLogSchwartz M hM W hW hW' ρ))
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at he
  change normDenominatorLogSchwartz M hM W hW hW' ρ (Real.log x-Real.log y) = _
  rw [← he]
  apply integral_congr_ae
  filter_upwards with t
  have hi : inner ℝ t (Real.log x-Real.log y) = t*Real.log x-t*Real.log y := by
    simp only [RCLike.inner_apply,conj_trivial]
    ring
  have hp : (Real.fourierChar (inner ℝ t (Real.log x-Real.log y)):ℂ) =
      gramMellinPhase t x*star (gramMellinPhase t y) := by
    rw [hi,AddChar.map_sub_eq_div,div_eq_mul_inv,Circle.coe_mul,Circle.coe_inv_eq_conj]
    rfl
  change (Real.fourierChar (inner ℝ t (Real.log x-Real.log y)):ℂ)*
    normDenominatorMellinCoefficient M hM W hW hW' ρ t = _
  rw [hp]
  ring

lemma exp_half_log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp ((Real.log x-Real.log y)/2) = Real.sqrt x/Real.sqrt y := by
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hx,Real.rpow_def_of_pos hy,← Real.exp_sub]
  congr 1
  ring

theorem normDenominator_radial_div_sqrt (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ}
    (hρ : 0 ≤ ρ) (hx : 0 < x) (hy : 0 < y) (hxy : |Real.log x-Real.log y| ≤ M) :
    radialDualProfile W (ρ*x/y)/(Real.sqrt y:ℂ) = ∫ t : ℝ,
      (Real.sqrt x:ℂ)⁻¹*normDenominatorMellinCoefficient M hM W hW hW' ρ t*
        gramMellinPhase t x*star (gramMellinPhase t y) := by
  have he := normDenominator_radial_mellin_separated M hM W hW hW' hρ hx hy hxy
  rw [exp_half_log_ratio hx hy,Complex.ofReal_div] at he
  calc
    _ = (Real.sqrt x:ℂ)⁻¹ * ((Real.sqrt x:ℂ)/(Real.sqrt y:ℂ)*radialDualProfile W (ρ*x/y)) := by
      have hs : (Real.sqrt x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
      field_simp
    _ = _ := by
      rw [he,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormCoprimeMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Mellin separation of the Poisson form including its
square-root norm denominator. The character rows retain their original weights. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normDenominatorMellinCoefficient_integrable_phases (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ x y : ℝ) :
    Integrable (fun t => normDenominatorMellinCoefficient M hM W hW hW' ρ t * gramMellinPhase t x *
      star (gramMellinPhase t y)) := by
  apply Integrable.mul_bdd (c := 1)
  · exact (normDenominatorMellinCoefficient_integrable M hM W hW hW' ρ).mul_bdd
      (gramMellinPhase_continuous x).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_gramMellinPhase t x).le))
  · exact (gramMellinPhase_continuous y).star.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp)


theorem normCoprimeRadialForm_mellin (M : ℝ) (hM : 0 < M) (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, 0 < x h)
    (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    normCoprimeRadialForm S H v w phase x y W ρ = ∫ t : ℝ,
      normDenominatorMellinCoefficient M hM W hW hW' ρ t * coprimeMellinKernel S H v w (fun h => phase h*(Real.sqrt (x h):ℂ)⁻¹) x y t := by
  let F (h a b : Eisenstein) (t : ℝ) : ℂ :=
    (phase h*(Real.sqrt (x h):ℂ)⁻¹ * (if IsCoprime a b then
      (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0)) *
      (normDenominatorMellinCoefficient M hM W hW hW' ρ t * gramMellinPhase t (x h) *
        star (gramMellinPhase t (y a*y b)))
  have hF (h a b : Eisenstein) : Integrable (F h a b) :=
    (normDenominatorMellinCoefficient_integrable_phases M hM W hW hW' ρ (x h) (y a*y b)).const_mul _
  have he (h : Eisenstein) (hh : h ∈ H) (a : Eisenstein) (ha : a ∈ S)
      (b : Eisenstein) (hb : b ∈ S) :
      phase h * (if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) *
          (radialDualProfile W (ρ*x h/(y a*y b))/(Real.sqrt (y a*y b):ℂ)) else 0) = ∫ t, F h a b t := by
    have hi := normDenominator_radial_div_sqrt M hM W hW hW' hρ (hx h hh)
      (mul_pos (hy a ha) (hy b hb)) (hlog h hh a ha b hb)
    have heq : (∫ t : ℝ, (Real.sqrt (x h):ℂ)⁻¹*
        normDenominatorMellinCoefficient M hM W hW hW' ρ t*
          gramMellinPhase t (x h)*star (gramMellinPhase t (y a*y b))) =
        (Real.sqrt (x h):ℂ)⁻¹*(∫ t : ℝ,
          normDenominatorMellinCoefficient M hM W hW hW' ρ t*
            gramMellinPhase t (x h)*star (gramMellinPhase t (y a*y b))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    rw [heq] at hi
    rw [hi]
    rw [show (∫ t, F h a b t) = _ from integral_const_mul _ _]
    split_ifs <;> ring
  calc
    _ = ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, ∫ t, F h a b t := by
      unfold normCoprimeRadialForm
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_congr rfl (fun b hb => he h hh a ha b hb)
    _ = ∫ t, ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, F h a b t := by
      rw [integral_finsetSum H (fun h _ =>
        integrable_finsetSum S (fun a _ => integrable_finsetSum S (fun b _ => hF h a b)))]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_finsetSum S (fun a _ => integrable_finsetSum S (fun b _ => hF h a b))]
      exact Finset.sum_congr rfl (fun a _ => (integral_finsetSum S (fun b _ => hF h a b)).symm)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      unfold coprimeMellinKernel
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [F]
      rw [gramMellinPhase_mul t (hy a ha)
        (hy b hb), star_mul]
      split_ifs <;> simp only [star_mul, mul_zero] <;> ring



lemma norm_denominator_phase_bound (H : Finset Eisenstein) (phase : Eisenstein → ℂ)
    (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1) (x : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, 1 ≤ x h) :
    ∀ h ∈ H, ‖phase h*(Real.sqrt (x h):ℂ)⁻¹‖ ≤ 1 := by
  intro h hh
  have hs : 0 < Real.sqrt (x h) := Real.sqrt_pos.mpr (zero_lt_one.trans_le (hx h hh))
  have hs₁ : 1 ≤ Real.sqrt (x h) := (Real.le_sqrt (by norm_num) (by linarith [hx h hh])).mpr
    (by simpa using hx h hh)
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs,← div_eq_mul_inv]
  exact (div_le_one hs).mpr ((hphase h hh).trans hs₁)

theorem normCoprimeRadialForm_norm_le_mass (M : ℝ) (hM : 0 < M) (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ) (hx : ∀ h ∈ H, 1 ≤ x h) (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖normCoprimeRadialForm S H v w phase x y W ρ‖ ≤
      ∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖*
        coprimeMellinMass S H U v w y t := by
  let phase' : Eisenstein → ℂ := fun h => phase h*(Real.sqrt (x h):ℂ)⁻¹
  have hphase' : ∀ h ∈ H, ‖phase' h‖ ≤ 1 := norm_denominator_phase_bound H phase hphase x hx
  have hc := normDenominatorMellinCoefficient_integrable M hM W hW hW' ρ
  have hi := hc.mul_bdd
    (coprimeMellinKernel_continuous S H v w phase' x y).aestronglyMeasurable
    (Eventually.of_forall (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase' hphase' x y))
  have hm := hc.norm.mul_bdd
    (coprimeMellinMass_continuous S H U v w y).aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (coprimeMellinMass_nonneg S H U v w y t)]
      exact coprimeMellinMass_le_envelope S H U (fun a ha => (hS a ha).1) v w y t))
  rw [normCoprimeRadialForm_mellin M hM S H v w phase x y
    (fun h hh => zero_lt_one.trans_le (hx h hh)) hy hlog W hW hW' hρ]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono hi.norm hm
  intro t
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_coprimeMellinKernel_le_mass S H U hS hU hSU v w phase' hphase' x y t)
    (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FinitePoissonRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of a finite Poisson frequency block with the
radial form used in the Mellin estimates, including its scalar. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma poisson_scaled_sqrt {L : ℝ} (hL : 0 < L) (a b : Eisenstein) :
    Real.sqrt ((norm a/L)*(norm b/L)) = Real.sqrt (norm (b*a))/L := by
  have he : (norm a/L)*(norm b/L) = norm (b*a)/L^2 := by
    rw [norm_mul_eq]
    ring
  rw [he,Real.sqrt_div (norm_nonneg _),Real.sqrt_sq hL.le]

theorem finitePoissonContribution_radial (S H : Finset Eisenstein)
    (hS : ∀ a ∈ S, a ≠ 0) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) {A L J : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hJ : 0 < J) :
    finitePoissonContribution S H β u W A =
      (A/(9*L):ℝ)*normCoprimeRadialForm S H
        (fun a => star (β a*mellinPhase u (norm a)))
        (fun a => star (β a*mellinPhase u (norm a)))
        (fun h => (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ))
        (fun h => norm h/J) (fun a => norm a/L) W (A*J/(27*L^2)) := by
  unfold finitePoissonContribution normCoprimeRadialForm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hc : IsCoprime b a ↔ IsCoprime a b := isCoprime_comm
  simp only [hc]
  split_ifs with hab
  · rw [gramDualTerm_radial a b W hA h]
    have harg : A*J/(27*L^2)*(norm h/J)/((norm a/L)*(norm b/L)) =
        A*norm h/(27*norm (a*b)) := by
      rw [norm_mul_eq]
      field_simp
    rw [harg,poisson_scaled_sqrt hL a b]
    simp only [star_mul,star_star,normTwist_eq_mellinPhase,Complex.ofReal_div,
      Complex.ofReal_mul,Complex.ofReal_ofNat]
    have hs : (Real.sqrt (norm (b*a)):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (mul_ne_zero (hS b hb) (hS a ha)))).ne'
    have hl : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    rw [mul_comm b a]
    field_simp
  · simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonEntryDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute decay of the literal Poisson summands outside the useful
frequency range. This estimate uses only the smooth compact profile. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace CubicFirstMoment

lemma gramDualTerm_norm_le_radial {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (V : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) (h : Eisenstein) :
    ‖gramDualTerm b a V A h‖ ≤ ‖radialDualProfile V (A*norm h/(27*norm (b*a)))‖ := by
  rw [gramDualTerm_radial b a V hA h,norm_mul]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  simp only [norm_mul,norm_star,Circle.norm_coe,mul_one]
  calc
    _ ≤ 1*1 := mul_le_mul (norm_cubicSymbol_le_one hb h) (norm_cubicSymbol_le_one ha h)
      (_root_.norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem poisson_entry_decay (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A L D J : ℝ), 0 < A → 0 < L → L ≤ D → 0 ≤ J →
      ∀ (a b h : Eisenstein), primary a → primary b →
      L ≤ norm a → norm a ≤ D → L ≤ norm b → norm b ≤ D → J ≤ norm h →
      ‖(A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h‖ ≤
        (A/(9*L))*C/(1+A*J/(27*D^2))^m := by
  obtain ⟨C,hC,hdecay⟩ := radialDualProfile_rapidDecay V hV hV' m
  refine ⟨C,hC,?_⟩
  intro A L D J hA hL hLD hJ a b h ha hb hLa haD hLb hbD hJh
  have hD : 0 < D := hL.trans_le hLD
  have hh0 : 0 ≤ norm h := norm_nonneg h
  have hN : 0 < norm (b*a) := norm_pos_of_ne_zero (mul_ne_zero (primary_ne_zero hb) (primary_ne_zero ha))
  have hupper : norm (b*a) ≤ D^2 := by
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul hbD haD (norm_nonneg a) hD.le
  have hlower : L^2 ≤ norm (b*a) := by
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul hLb hLa hL.le (norm_nonneg b)
  have hsqrt : L ≤ Real.sqrt (norm (b*a)) := (Real.le_sqrt hL.le hN.le).mpr hlower
  have harg : A*J/(27*D^2) ≤ A*norm h/(27*norm (b*a)) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJh hA.le) (by positivity)).trans
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have ht : 0 ≤ A*norm h/(27*norm (b*a)) := by positivity
  have hdec := hdecay _ ht
  have hrad : ‖radialDualProfile V (A*norm h/(27*norm (b*a)))‖ ≤ C/(1+A*J/(27*D^2))^m := by
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+A*J/(27*D^2)) m)).mpr
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity)
        (add_le_add (le_rfl : (1:ℝ) ≤ 1) harg) m)
      (_root_.norm_nonneg (radialDualProfile V (A*norm h/(27*norm (b*a)))))
    nlinarith
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (A/(9*L))*(C/(1+A*J/(27*D^2))^m) :=
      mul_le_mul (div_le_div_of_nonneg_left hA.le (by positivity) (by nlinarith))
        ((gramDualTerm_norm_le_radial ha hb V hA.le h).trans hrad)
        (_root_.norm_nonneg _) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonAbsoluteDyad
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute control of arbitrary subsets of a Poisson frequency annulus. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem finitePoissonContribution_absolute (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A L D J : ℝ), 0 < A → 0 < L → L ≤ D → 0 ≤ J →
      ∀ (S H : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ L ≤ norm a ∧ norm a ≤ D) →
      (∀ h ∈ H, J ≤ norm h) → ∀ (β : Eisenstein → ℂ) (u : ℝ),
      ‖finitePoissonContribution S H β u V A‖ ≤
        C*(A/(9*L))*(H.card:ℝ)*(∑ a ∈ S, ‖β a‖)^2/(1+A*J/(27*D^2))^m := by
  obtain ⟨C,hC,hentry⟩ := poisson_entry_decay V hV hV' m
  refine ⟨C,hC,?_⟩
  intro A L D J hA hL hLD hJ S H hS hH β u
  let E := (A/(9*L))*C/(1+A*J/(27*D^2))^m
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpair (h a b : Eisenstein) (hh : h ∈ H) (ha : a ∈ S) (hb : b ∈ S) :
      ‖(if IsCoprime a b then
        (β a*normTwist u a)*star (β b*normTwist u b)*
          (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h else 0)‖ ≤
        ‖β a‖*‖β b‖*E := by
    split_ifs
    · have heq : (β a*normTwist u a)*star (β b*normTwist u b)*
          (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h =
        ((β a*normTwist u a)*star (β b*normTwist u b))*
          ((A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h) := by ring
      rw [heq,norm_mul]
      simp only [norm_mul,norm_star,norm_normTwist,mul_one]
      have hp := hentry A L D J hA hL hLD hJ a b h (hS a ha).1 (hS b hb).1
        (hS a ha).2.1 (hS a ha).2.2 (hS b hb).2.1 (hS b hb).2.2 (hH h hh)
      simp only [norm_mul] at hp
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    · simp only [norm_zero]
      positivity
  unfold finitePoissonContribution
  calc
    _ ≤ ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, ‖β a‖*‖β b‖*E := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro h hh
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun b hb => hpair h a b hh ha hb)
    _ = _ := by
      simp only [← Finset.mul_sum,← Finset.sum_mul,Finset.sum_const,nsmul_eq_mul]
      dsimp [E]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.DirichletL_CubicDyadicDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

lemma dyadic_rpow (α : ℝ) (j : ℕ) :
    ((2 : ℝ)^j)^α = ((2 : ℝ)^α)^j := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]

lemma decay_le_low (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤ ((2 : ℝ)^α)^j := by
  rw [← dyadic_rpow]
  exact div_le_self (by positivity) (one_le_pow₀ (by
    have : 0 ≤ t * (2 : ℝ)^j := by positivity
    linarith))

lemma decay_le_high (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α - 3))^j := by
  have hk : 0 < (2 : ℝ)^j := by positivity
  calc
    _ ≤ ((2 : ℝ)^j)^α / (t * (2 : ℝ)^j)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 3)
    _ = _ := by
      rw [← dyadic_rpow, Real.rpow_sub hk, Real.rpow_neg ht.le, mul_pow]
      simp only [Real.rpow_ofNat]
      ring

lemma decay_summable (t α : ℝ) (ht : 0 < t) (hα : α < 3) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) := by
  have hr : (2 : ℝ)^(α - 3) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact ((summable_geometric_of_lt_one (by positivity) hr).mul_left (t^(-3 : ℝ))).of_nonneg_of_le
    (fun j => by positivity) (decay_le_high t α ht)

lemma decayConstant_pos (α : ℝ) (hα : 0 < α) (hα3 : α < 3) :
    0 < decayConstant α := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold decayConstant
  positivity

lemma geometric_prefix_le (q : ℝ) (hq : 1 < q) (k : ℕ) :
    (∑ j ∈ Finset.range k, q^j) ≤ q^k / (q - 1) := by
  rw [geom_sum_eq (ne_of_gt hq)]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma decay_tail_le (t α : ℝ) (ht : 0 < t) (hα3 : α < 3) (k : ℕ) :
    (∑' j : ℕ, ((2 : ℝ)^(j+k))^α / (1 + t * (2 : ℝ)^(j+k))^3) ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k * (1 - (2 : ℝ)^(α-3))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^(α-3) := by positivity
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs := summable_geometric_of_lt_one hr0 hr
  calc
    _ ≤ ∑' j : ℕ, t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^(j+k) := by
      apply (decay_summable t α ht hα3).comp_injective (add_left_injective k) |>.tsum_le_tsum
        (fun j => decay_le_high t α ht (j+k))
      exact (hs.comp_injective (add_left_injective k)).mul_left _
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr]
      ring

theorem dyadic_decay_bound (t α : ℝ) (ht : 0 < t) (hα : 0 < α) (hα3 : α < 3) :
    (∑' j : ℕ, ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
      decayConstant α * t^(-α) := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < (1 - (2 : ℝ)^(α-3))⁻¹ := inv_pos.mpr (by linarith)
  by_cases ht1 : 1 ≤ t
  · have hp : t^(-3 : ℝ) ≤ t^(-α) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hh := decay_tail_le t α ht hα3 0
    simp only [Nat.add_zero, pow_zero, mul_one] at hh
    apply hh.trans
    unfold decayConstant
    nlinarith [mul_nonneg (div_nonneg (by positivity : 0 ≤ (2 : ℝ)^α)
      (by linarith : 0 ≤ (2 : ℝ)^α - 1)) (by positivity : 0 ≤ t^(-α)),
      mul_le_mul_of_nonneg_right hp hden.le]
  · have hit : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr (le_of_not_ge ht1)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hit (by norm_num : (1 : ℝ) < 2)
    let k := n+1
    have hk0 : 0 < (2 : ℝ)^k := by positivity
    have hk : t⁻¹ ≤ (2 : ℝ)^k := le_of_lt hn'
    have hk' : (2 : ℝ)^k ≤ 2*t⁻¹ := by
      dsimp [k]
      rw [pow_succ]
      nlinarith
    have hlow : (∑ j ∈ Finset.range k,
        ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
        (2 : ℝ)^α / ((2 : ℝ)^α - 1) * t^(-α) := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, ((2 : ℝ)^α)^j :=
          Finset.sum_le_sum (fun j hj => decay_le_low t α ht j)
        _ ≤ ((2 : ℝ)^α)^k / ((2 : ℝ)^α - 1) := geometric_prefix_le _ hq k
        _ ≤ (2*t⁻¹)^α / ((2 : ℝ)^α - 1) := by
          rw [← dyadic_rpow]
          exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hk0.le hk' hα.le)
            (by linarith)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr ht.le),
            ← Real.rpow_neg_eq_inv_rpow]
          ring
    have hhigh : t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k ≤ t^(-α) := by
      rw [← dyadic_rpow]
      calc
        _ ≤ t^(-3 : ℝ) * (t⁻¹)^(α-3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ht)
            hk (by linarith)) (by positivity)
        _ = _ := by
          rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_add ht]
          congr 1
          ring
    rw [← (decay_summable t α ht hα3).sum_add_tsum_nat_add k]
    have htail := (decay_tail_le t α ht hα3 k).trans
      (mul_le_mul_of_nonneg_right hhigh hden.le)
    unfold decayConstant
    nlinarith

end
end SevenEighths.CubicDyadicDecay

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonTailSum
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily rapid tails of the actual dyadic Poisson envelope. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_tsum_prefix_tail {F : ℕ → ℂ} (n : ℕ) {A B : ℝ}
    (hf : Summable (fun j => F (j+n)))
    (hprefix : ‖∑ j ∈ Finset.range n, F j‖ ≤ A)
    (htail : ‖∑' j : ℕ, F (j+n)‖ ≤ B) : ‖∑' j : ℕ, F j‖ ≤ A+B := by
  have hs : Summable F := hf.comp_nat_add
  rw [← hs.sum_add_tsum_nat_add n]
  exact (norm_add_le _ _).trans (add_le_add hprefix htail)

lemma poisson_dyadic_tail_majorant {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (m n j : ℕ) :
    C*(2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^(m+3) ≤
      (C/(t*(2:ℝ)^n)^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) := by
  have hpow : (2:ℝ)^n ≤ (2:ℝ)^(j+n) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_add_left n j)
  have hbase : t*(2:ℝ)^n ≤ 1+t*(2:ℝ)^(j+n) := by nlinarith
  calc
    _ = (C/(1+t*(2:ℝ)^(j+n))^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) := by
      rw [pow_add]
      field_simp
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ (by positivity) hbase m))
      (by positivity)

theorem poisson_dyadic_tail {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (m n : ℕ) (F : ℕ → ℂ)
    (hF : ∀ j, ‖F j‖ ≤ C*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3)) :
    Summable (fun j => F (j+n)) ∧
      ‖∑' j : ℕ, F (j+n)‖ ≤
        (C/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  have hs := (SevenEighths.CubicDyadicDecay.decay_summable t 1 ht (by norm_num)).comp_injective
    (add_left_injective n)
  simp only [Real.rpow_one] at hs
  have hm := hs.mul_left (C/(t*(2:ℝ)^n)^m)
  have hb (j : ℕ) : ‖F (j+n)‖ ≤
      (C/(t*(2:ℝ)^n)^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) :=
    (hF (j+n)).trans (poisson_dyadic_tail_majorant ht hC m n j)
  have hsum : Summable (fun j => F (j+n)) := hm.of_norm_bounded hb
  refine ⟨hsum,?_⟩
  have ht' := SevenEighths.CubicDyadicDecay.decay_tail_le t 1 ht (by norm_num) n
  norm_num only [Real.rpow_one,show (1:ℝ)-3 = -2 by norm_num] at ht'
  calc
    _ ≤ ∑' j : ℕ, ‖F (j+n)‖ := norm_tsum_le_tsum_norm (hm.of_nonneg_of_le (fun _ => _root_.norm_nonneg _) hb)
    _ ≤ ∑' j : ℕ, (C/(t*(2:ℝ)^n)^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) :=
      Summable.tsum_le_tsum hb (hm.of_nonneg_of_le (fun _ => _root_.norm_nonneg _) hb) hm
    _ = (C/(t*(2:ℝ)^n)^m)*(∑' j : ℕ, (2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) := tsum_mul_left
    _ ≤ _ := by
      have htwo : (2:ℝ)^(-2:ℝ) = 1/4 := by norm_num
      simpa only [htwo,show ((1:ℝ)-1/4)⁻¹ = 4/3 by norm_num] using
        mul_le_mul_of_nonneg_left ht' (show 0 ≤ C/(t*(2:ℝ)^n)^m by positivity)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonDyadicSum
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the annular noncube estimate at its natural Poisson scale. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_poisson_scale {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    A*L*(A/(27*L^2))^(-(1/3:ℝ)) = 3*A^(2/3:ℝ)*L^(5/3:ℝ) := by
  have h27 : (27:ℝ)^(1/3:ℝ) = 3 := by
    rw [show (27:ℝ) = 3^3 by norm_num,← Real.rpow_natCast (3:ℝ) 3,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [Real.div_rpow hA.le (by positivity : 0 ≤ 27*L^2),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 27) (sq_nonneg L),
    Real.rpow_neg hA.le,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 27),
    Real.rpow_neg (sq_nonneg L),h27,← Real.rpow_natCast L 2,
    ← Real.rpow_mul hL.le]
  have hAa : A/A^(1/3:ℝ) = A^(2/3:ℝ) := by
    nth_rw 1 [← Real.rpow_one A]
    rw [← Real.rpow_sub hA]
    norm_num
  have hLa : L*L^((2:ℝ)*(1/3)) = L^(5/3:ℝ) := by
    nth_rw 1 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    norm_num
  calc
    _ = 3*(A/A^(1/3:ℝ))*(L*L^((2:ℝ)*(1/3))) := by field_simp; norm_num
    _ = _ := by rw [hAa,hLa]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonGramRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the coprime term from the exact common-factor expansion.
Only nonunit common factors remain, so roughness shortens every row. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma commonGramBlock_moebius (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) {k : Eisenstein} (hk : primary k) (hsk : Squarefree k) :
    commonGramBlock S u W Z k = ∑ s ∈ (primaryPrimeFactors k).powerset,
      let m := ∏ p ∈ s, p
      (idealMoebius m:ℂ)*coprimeGramForm (residualRows S k)
        (commonBlockCoefficient u k m) W (Z/norm m) := by
  have hr := residualRows_primary hk hS
  unfold commonGramBlock
  calc
    _ = ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        ∑ s ∈ (primaryPrimeFactors k).powerset,
          let m := ∏ p ∈ s, p
          (idealMoebius m:ℂ)*(if IsCoprime a b then commonBlockCoefficient u k m a*
            star (commonBlockCoefficient u k m b)*primaryCharacterGram a b W (Z/norm m)
            else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab : IsCoprime a b
      · simp only [ite_eq_left hab]
        rw [primaryCharacterGram_common_factor hk hsk (hr a ha).1 (hr b hb).1 W hW hW' hZ,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        simp only [commonBlockCoefficient,mixedSymbol,star_mul]
        ring
      · simp [hab]
    _ = _ := by
      simp_rw [Finset.sum_comm (s := residualRows S k) (t := (primaryPrimeFactors k).powerset)]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [coprimeGramForm,Finset.mul_sum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightMeanSquare
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightCoprimeContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domination and continuity for the genuine divisor-restricted mass
as its independent arithmetic height varies. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma coprimeMellinMass_continuous_coefficients (S H U : Finset Eisenstein)
    (v w : ℝ → Eisenstein → ℂ) (hv : ∀ a, Continuous (fun t => v t a))
    (hw : ∀ a, Continuous (fun t => w t a)) (y : Eisenstein → ℝ) (s : ℝ) :
    Continuous (fun t => coprimeMellinMass S H U (v t) (w t) y s) := by
  unfold coprimeMellinMass
  apply continuous_finsetSum
  intro d hd
  apply Continuous.div_const
  apply Continuous.add
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact ((hv a).mul continuous_const).mul continuous_const
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact ((hw a).mul continuous_const).mul continuous_const

lemma normCoprimeRadialForm_continuous_coefficients (S H : Finset Eisenstein)
    (v w : ℝ → Eisenstein → ℂ) (hv : ∀ a, Continuous (fun t => v t a))
    (hw : ∀ a, Continuous (fun t => w t a)) (phase : Eisenstein → ℂ)
    (x y : Eisenstein → ℝ) (W : ℝ → ℂ) (ρ : ℝ) :
    Continuous (fun t => normCoprimeRadialForm S H (v t) (w t) phase x y W ρ) := by
  unfold normCoprimeRadialForm
  apply continuous_finsetSum
  intro h hh
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact (((hv a).mul continuous_const).mul ((hw b).mul continuous_const).star).mul continuous_const
  · exact continuous_const

lemma twistedCoprimeMellinMass_continuous_height (S H U : Finset Eisenstein)
    (β : Eisenstein → ℂ) (y : Eisenstein → ℝ) (s : ℝ) :
    Continuous (fun u => twistedCoprimeMellinMass S H U β y u s) := by
  apply coprimeMellinMass_continuous_coefficients
  all_goals intro a; unfold mellinPhase; fun_prop

lemma twistedCoprimeMellinMass_le (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ) (y : Eisenstein → ℝ) (u s : ℝ) :
    twistedCoprimeMellinMass S H U β y u s ≤ coprimeMellinEnvelope S H U β β := by
  have h := coprimeMellinMass_le_envelope S H U hS
    (fun a => star (β a*mellinPhase u (norm a)))
    (fun a => star (β a*mellinPhase u (norm a))) y s
  simpa only [twistedCoprimeMellinMass,coprimeMellinEnvelope,norm_star,norm_mul,mellinPhase_norm,mul_one] using h

lemma continuous_integral_twistedCoprimeMellinMass (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ) (y : Eisenstein → ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) :
    Continuous (fun u => ∫ s : ℝ, f s*twistedCoprimeMellinMass S H U β y u s) := by
  apply continuous_of_dominated (bound := fun s => ‖f s‖*coprimeMellinEnvelope S H U β β)
  · intro u
    exact (hf.mul (coprimeMellinMass_continuous S H U _ _ y)).aestronglyMeasurable
  · intro u
    filter_upwards with s
    have hn : 0 ≤ twistedCoprimeMellinMass S H U β y u s :=
      coprimeMellinMass_nonneg S H U _ _ y s
    rw [norm_mul,Real.norm_eq_abs (twistedCoprimeMellinMass S H U β y u s),abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (twistedCoprimeMellinMass_le S H U hS β y u s)
      (_root_.norm_nonneg _)
  · exact hfi.norm.mul_const _
  · filter_upwards with s
    exact continuous_const.mul (twistedCoprimeMellinMass_continuous_height S H U β y s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightPoissonAnnulus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine finite Poisson contribution inherits the averaged
annular estimate with its exact geometric scalar A/(9L). -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finitePoissonContribution_continuous_height (S H : Finset Eisenstein)
    (β : Eisenstein → ℂ) (V : ℝ → ℂ) (A : ℝ) :
    Continuous (fun u => finitePoissonContribution S H β u V A) := by
  unfold finitePoissonContribution
  apply continuous_finsetSum
  intro h hh
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact ((((continuous_const.mul (continuous_normTwist a)).mul
      (continuous_const.mul (continuous_normTwist b)).star).mul continuous_const).mul continuous_const)
  · exact continuous_const

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightPoissonDyadic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma averaged_cubic_dyadic_sum (I : Finset ℕ) (F : ℕ → ℝ → ℂ)
    (hF : ∀ i ∈ I, Continuous (F i)) {C t T : ℝ} (hC : 0 ≤ C) (ht : 0 < t) (hT : 0 < T)
    (hbound : ∀ j ∈ I, dyadicHeightMean (fun u => ‖F j u‖) T ≤
      C*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3) :
    dyadicHeightMean (fun u => ‖∑ j ∈ I, F j u‖) T ≤
      C*SevenEighths.CubicDyadicDecay.decayConstant (1/3)*t^(-(1/3:ℝ)) := by
  have hs := SevenEighths.CubicDyadicDecay.decay_summable t (1/3) ht (by norm_num)
  have hb := SevenEighths.CubicDyadicDecay.dyadic_decay_bound t (1/3) ht (by norm_num) (by norm_num)
  calc
    _ ≤ ∑ j ∈ I, dyadicHeightMean (fun u => ‖F j u‖) T := dyadicHeightMean_norm_sum_le I F hF hT
    _ ≤ ∑ j ∈ I, C*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := Finset.sum_le_sum hbound
    _ = C*(∑ j ∈ I, ((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ C*(∑' j : ℕ, ((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3) :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum I (fun j _ => by positivity)) hC
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC

lemma continuous_poisson_series (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
    (β : Eisenstein → ℂ) (V : ℝ → ℂ) (A u : ℝ) {C t : ℝ} (ht : 0 < t)
    (hbound : ∀ j v, ‖finitePoissonContribution S (H j) β (u+v) V A‖ ≤
      C*(2:ℝ)^j/(1+t*2^j)^3) :
    Continuous (fun v => ∑' j : ℕ, finitePoissonContribution S (H j) β (u+v) V A) := by
  have hs := SevenEighths.CubicDyadicDecay.decay_summable t 1 ht (by norm_num)
  simp only [Real.rpow_one] at hs
  apply continuous_tsum (fun j => (finitePoissonContribution_continuous_height S (H j) β V A).comp
    (continuous_const.add continuous_id)) (hs.mul_left C)
  intro j v
  simpa only [Function.comp_apply,Pi.add_apply,id_eq,mul_div_assoc] using hbound j v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimePoissonSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the complete nonzero dyadic Poisson series with the
original coprime portion of the dispersion Gram form. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimeDispersionGram_eq_poisson_series (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ a ≠ 1)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    coprimeDispersionGram S β u V A =
      ∑' j : ℕ, finitePoissonContribution S (frequencyDyad j) β u V A := by
  let G := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h else 0
  let F := fun h => ∑ a ∈ S, ∑ b ∈ S, G a b h
  have hG (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) : Summable (G a b) := by
    by_cases hab : IsCoprime a b
    · simpa only [G,ite_eq_left hab] using
        (summable_gramDualTerm (hS b hb).1 (hS a ha).1 V hV hV' hA).mul_left
          ((β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ))
    · simp only [G,ite_eq_right hab]
      exact summable_zero
  have hF : Summable F := summable_sum (fun a ha => summable_sum (fun b hb => hG a b ha hb))
  have hF0 : F 0 = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hab : IsCoprime a b
    · have hne : b ≠ a := by
        intro hba
        exact (hS a ha).2.2 (primary_unit_eq_one (isCoprime_self.mp (hba ▸ hab)) (hS a ha).1)
      simp only [G,ite_eq_left hab,
        gramDualTerm_zero (hS b hb).1 (hS a ha).1 (hS b hb).2.1 (hS a ha).2.1 hab.symm hne V A,
        mul_zero]
    · simp only [G,ite_eq_right hab]
  have hb := hasSum_frequencyDyad F hF hF0
  change HasSum (fun j => finitePoissonContribution S (frequencyDyad j) β u V A) (∑' h, F h) at hb
  rw [hb.tsum_eq]
  rw [show (∑' h, F h) = ∑ a ∈ S, ∑ b ∈ S, ∑' h, G a b h from by
    dsimp only [F]
    rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hG a b ha hb))]
    exact Finset.sum_congr rfl (fun a ha => Summable.tsum_finsetSum (fun b hb => hG a b ha hb))]
  unfold coprimeDispersionGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [G,ite_eq_left hab,tsum_mul_left]
    rw [dispersion_pair_poisson (hS a ha).1 (hS b hb).1 (hS a ha).2.1 (hS b hb).2.1
      hab β u V hV hV' hA]
    simp only [star_mul]
    ring
  · simp only [G,ite_eq_right hab,tsum_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBPoissonScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalization of the small-B Poisson bound on one dyadic
coefficient interval. -/
noncomputable section
namespace CubicFirstMoment

lemma arbitrary_poisson_scale {A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    (A/N)*(A/(27*N^2))^(-(1/3:ℝ)) =
      3*A^(2/3:ℝ)*N^(-(1/3:ℝ)) := by
  apply (mul_right_inj' (sq_pos_of_pos hN).ne').mp
  calc
    _ = A*N*(A/(27*N^2))^(-(1/3:ℝ)) := by field_simp
    _ = 3*A^(2/3:ℝ)*N^(5/3:ℝ) := cubic_poisson_scale hA hN
    _ = _ := by
      have he : N^(5/3:ℝ) = N^2*N^(-(1/3:ℝ)) := by
        rw [← Real.rpow_natCast N 2,← Real.rpow_add hN]
        norm_num
      rw [he]
      ring

lemma smallB_dyadic_poisson_scale {A Z : ℝ} (hA : 0 < A) (hZ : 0 < Z) :
    (A/(Z/2))*Z^(1-1/40000:ℝ)*(A/(27*(Z/2)^2))^(-(1/3:ℝ)) =
      (3*(2:ℝ)^(1/3:ℝ))*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ) := by
  calc
    _ = Z^(1-1/40000:ℝ)*((A/(Z/2))*(A/(27*(Z/2)^2))^(-(1/3:ℝ))) := by ring
    _ = Z^(1-1/40000:ℝ)*(3*A^(2/3:ℝ)*(Z/2)^(-(1/3:ℝ))) := by
      rw [arbitrary_poisson_scale hA (by positivity : 0 < Z/2)]
    _ = Z^(1-1/40000:ℝ)*(3*A^(2/3:ℝ)*
        (Z^(-(1/3:ℝ))*(2:ℝ)^(1/3:ℝ))) := by
      rw [Real.div_rpow hZ.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
    _ = (3*(2:ℝ)^(1/3:ℝ))*A^(2/3:ℝ)*
        (Z^(1-1/40000:ℝ)*Z^(-(1/3:ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add hZ]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBPoissonEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An absolute Poisson envelope and its actual infinite tail for
arbitrary coefficients, in terms of their exact quadratic energy. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem arbitrary_poisson_dyad_energy (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (A N Z u : ℝ) (j : ℕ), 0 < A → 0 < N → N ≤ Z →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) → H ⊆ frequencyDyad j →
      ‖finitePoissonContribution S H β u V A‖ ≤
        K*(A/N)*Z*(∑ a ∈ S, ‖β a‖^2)*(2:ℝ)^j/(1+A*(2:ℝ)^j/(27*Z^2))^m := by
  obtain ⟨C,hC,hbound⟩ := finitePoissonContribution_absolute V hV hV' m
  refine ⟨72*C,by positivity,?_⟩
  intro S H β A N Z u j hA hN hNZ hS hH
  have hZ : 0 < Z := hN.trans_le hNZ
  have hcard := primary_support_card_le S hZ.le (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun a => ‖β a‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  have he : (∑ a ∈ S, ‖β a‖)^2 ≤ 18*Z*∑ a ∈ S, ‖β a‖^2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hh : (H.card:ℝ) ≤ 36*(2:ℝ)^j :=
    (show (H.card:ℝ) ≤ (frequencyDyad j).card from by exact_mod_cast Finset.card_le_card hH).trans
      (frequencyDyad_card_le j)
  have hb := hbound A N Z ((2:ℝ)^j) hA hN hNZ (by positivity) S H hS
    (fun h hmem => (frequencyDyad_norm (hH hmem)).1) β u
  calc
    _ ≤ C*(A/(9*N))*(36*(2:ℝ)^j)*(18*Z*∑ a ∈ S, ‖β a‖^2)/
        (1+A*(2:ℝ)^j/(27*Z^2))^m := by
      apply hb.trans
      gcongr
    _ = _ := by ring

theorem arbitrary_poisson_energy_tail (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ), 0 < A → 0 < N → N ≤ Z →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ frequencyDyad j) →
      let t := A/(27*Z^2)
      Summable (fun j => finitePoissonContribution S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution S (H (j+n)) β u V A‖ ≤
        (K*(A/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  obtain ⟨K,hK,hbound⟩ := arbitrary_poisson_dyad_energy V hV hV' (m+3)
  refine ⟨K,hK,?_⟩
  intro S H β A N Z u n hA hN hNZ hS hH
  have hZ : 0 < Z := hN.trans_le hNZ
  let t := A/(27*Z^2)
  let E := K*(A/N)*Z*∑ a ∈ S, ‖β a‖^2
  have ht : 0 < t := by dsimp [t]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hr (j : ℕ) : ‖finitePoissonContribution S (H j) β u V A‖ ≤
      E*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3) := by
    have he : t*(2:ℝ)^j = A*(2:ℝ)^j/(27*Z^2) := by dsimp [t]; ring
    dsimp only [E]
    rw [he]
    exact hbound S (H j) β A N Z u j hA hN hNZ hS (hH j)
  exact poisson_dyadic_tail ht hE m n
    (fun j => finitePoissonContribution S (H j) β u V A) hr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonHeightCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the normalized Gauss factor without changing coefficient energy.
This permits the proved dispersion estimate to act on the literal
common-factor rows, with their original height dependence. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma gramUntwist_norm {a : Eisenstein} (ha : primary a) (hs : Squarefree a)
    (v : Eisenstein → ℂ) : ‖gramUntwist v a‖ = ‖v a‖ := by
  simp only [gramUntwist,norm_mul,norm_star,norm_gauss ha,ite_eq_left hs,mul_one]

lemma gramUntwist_amplitude {a : Eisenstein} (ha : primary a) (hs : Squarefree a)
    (v : Eisenstein → ℂ) (u : ℝ) :
    star (dispersionAmplitude (gramUntwist v) u a) = v a*star (normTwist u a) := by
  have hg : gauss a*star (gauss a) = 1 := by
    simpa only [ite_eq_left hs] using gauss_mul_star_squarefree ha
  simp only [dispersionAmplitude,gramUntwist,star_mul,star_star]
  calc
    _ = (v a*star (normTwist u a))*(gauss a*star (gauss a)) := by ring
    _ = _ := by rw [hg,mul_one]

lemma coprimeGramForm_height_eq (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (v : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    coprimeGramForm S (fun a => v a*star (normTwist u a)) W A =
      coprimeDispersionGram S (gramUntwist v) u W A := by
  unfold coprimeGramForm coprimeDispersionGram
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,ite_eq_left hab.symm]
    rw [← gramUntwist_amplitude (hS a ha).1 (hS a ha).2,
      ← gramUntwist_amplitude (hS b hb).1 (hS b hb).2,star_star]
    ring
  · simp only [ite_eq_right hab,ite_eq_right (fun h : IsCoprime b a => hab h.symm)]

lemma coprimeGramForm_unit_scalar (S : Finset Eisenstein) (v : Eisenstein → ℂ)
    {c : ℂ} (hc : ‖c‖ = 1) (W : ℝ → ℂ) (A : ℝ) :
    coprimeGramForm S (fun a => c*v a) W A = coprimeGramForm S v W A := by
  have hcc : c*star c = 1 := by
    simpa only [starRingEnd_apply,hc,one_pow,Complex.ofReal_one] using Complex.mul_conj' c
  unfold coprimeGramForm
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs
  · simp only [star_mul]
    calc
      _ = (c*star c)*(v a*star (v b)*primaryCharacterGram a b W A) := by ring
      _ = _ := by rw [hcc,one_mul]
  · rfl

lemma commonBlockCoefficient_height (β : Eisenstein → ℂ) (k m : Eisenstein)
    {a : Eisenstein} (hk : primary k) (ha : primary a) (u : ℝ) :
    commonBlockCoefficient (fun b => star (dispersionAmplitude β u b)) k m a =
      star (normTwist u k)*
        (commonBlockCoefficient (fun b => star (β b*gauss b)) k m a *
          star (normTwist u a)) := by
  simp only [commonBlockCoefficient,dispersionAmplitude,
    normTwist_mul u (primary_ne_zero hk) (primary_ne_zero ha),star_mul]
  ring

lemma common_coprime_height_eq (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (k m : Eisenstein) (hk : primary k)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    coprimeGramForm (residualRows S k)
        (commonBlockCoefficient (fun b => star (dispersionAmplitude β u b)) k m) W A =
      coprimeDispersionGram (residualRows S k)
        (gramUntwist (commonBlockCoefficient (fun b => star (β b*gauss b)) k m)) u W A := by
  have hr := residualRows_primary hk hS
  calc
    _ = coprimeGramForm (residualRows S k) (fun a => star (normTwist u k)*
        (commonBlockCoefficient (fun b => star (β b*gauss b)) k m a *
          star (normTwist u a))) W A := by
      unfold coprimeGramForm
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [commonBlockCoefficient_height β k m hk (hr a ha).1,
        commonBlockCoefficient_height β k m hk (hr b hb).1]
    _ = _ := (coprimeGramForm_unit_scalar _ _ (by simp) W A).trans
      (coprimeGramForm_height_eq _ hr _ u W A)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightGramContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma continuous_coprimeDispersionGram (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (V : ℝ → ℂ) (A : ℝ) : Continuous (fun u => coprimeDispersionGram S β u V A) := by
  unfold coprimeDispersionGram
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact ((continuous_dispersionAmplitude β a).mul (continuous_dispersionAmplitude β b).star).mul continuous_const
  · exact continuous_const

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailRadialForm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual norm-denominator Poisson form for arbitrary squarefree
coefficients. No convolution or smoothness of the coefficients is required. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeGroupTail_radial_form_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) {R : ℝ} (hR : 1 ≤ R)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β phase : Eisenstein → ℂ)
      (Z : ℕ) (B T u ρ N J : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 ≤ ρ → 0 < N → 0 < J →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) R) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) → (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      (1+ρ)^q*dyadicHeightMean (fun t =>
        ‖normCoprimeRadialForm S H
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          phase (fun h => norm h/J) (fun a => norm a/N) V ρ‖) T ≤
        K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  let M := 1+2*Real.log R
  have hM : 0 < M := by dsimp [M]; linarith [Real.log_nonneg hR]
  obtain ⟨K,hK,hmass⟩ := primeGroupTail_coprime_mellin_height_power hMV hC hHuxley
    M hM V hV hV' q
  refine ⟨K,hK,?_⟩
  intro S H β phase Z B T u ρ N J hZ hB hT hρ hN hJ hS hrange hsize hH hHJ hphase
  let U := S.biUnion primaryPrimeFactors
  have hU : ∀ p ∈ U, primaryPrime p := by
    intro p hp
    obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp hp
    exact (primaryPrimeFactor_spec (hS a ha).1 hpa).1
  have hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U := by
    intro a ha p hp
    exact Finset.mem_biUnion.mpr ⟨a,ha,hp⟩
  let v := fun t (a : Eisenstein) => star (β a*mellinPhase (t+u) (norm a))
  have hvc (a : Eisenstein) : Continuous (fun t => v t a) := by
    dsimp [v,mellinPhase]
    fun_prop
  have hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S,
      |Real.log (norm h/J)-Real.log ((norm a/N)*(norm b/N))| ≤ M := by
    intro h hh a ha b hb
    exact compact_norm_log_ratio hR
      ⟨(le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1),
        (div_le_iff₀ hJ).mpr (hHJ h hh).2⟩ (hrange a ha) (hrange b hb)
  have hn (t : ℝ) := normCoprimeRadialForm_norm_le_mass M hM S H U
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) hU hSU
    (v t) (v t) phase hphase (fun h => norm h/J) (fun a => norm a/N)
    (fun h hh => (le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1))
    (fun a ha => zero_lt_one.trans_le (hrange a ha).1) hlog V hV hV' hρ
  have hf := normCoprimeRadialForm_continuous_coefficients S H v v hvc hvc
    phase (fun h => norm h/J) (fun a => norm a/N) V ρ
  have hg := continuous_integral_twistedCoprimeMellinMass S H U
    (fun a ha => (hS a ha).1) β (fun a => norm a/N)
    (𝓕 (normDenominatorLogSchwartz M hM V hV hV' ρ)).continuous.norm
    (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
  have hTp : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hT
  have hh := dyadicHeightMean_mono hf.norm (hg.comp (continuous_id.add continuous_const)) hTp
    (fun t _ => hn t)
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans
    (hmass S H U β Z B T u ρ N hZ hB hT hρ hN hU hS hsize hH)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailPoissonAnnulus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite Poisson annulus, with arbitrary squarefree coefficients,
in the small-B range. No restriction on the translated arithmetic height. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_poisson_annulus_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) {R : ℝ} (hR : 1 ≤ R)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (A B T u N J : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 < A → 0 < N → 0 < J →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) R) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) →
      (1+A*J/(27*N^2))^q*dyadicHeightMean (fun t =>
        ‖finitePoissonContribution S H β (u+t) V A‖) T ≤
        K*(A/N)*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_radial_form_height_power hMV hC hHuxley hR V hV hV' q
  refine ⟨K/9,by positivity,?_⟩
  intro S H β Z A B T u N J hZ hB hT hA hN hJ hS hrange hsize hH hHJ
  let phase := fun h : Eisenstein =>
    (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ)
  have hb := hbound S H β phase Z B T u (A*J/(27*N^2)) N J
    hZ hB hT (by positivity) hN hJ hS hrange hsize hH hHJ
    (fun h _ => (Circle.norm_coe _).le)
  have heq (t : ℝ) : ‖finitePoissonContribution S H β (u+t) V A‖ =
      (A/(9*N))*‖normCoprimeRadialForm S H
        (fun a => star (β a*mellinPhase (t+u) (norm a)))
        (fun a => star (β a*mellinPhase (t+u) (norm a)))
        phase (fun h => norm h/J) (fun a => norm a/N) V (A*J/(27*N^2))‖ := by
    rw [finitePoissonContribution_radial S H
      (fun a ha => primary_ne_zero (hS a ha).1) β (u+t) V hA.le hN hJ,
      norm_mul,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ A/(9*N) by positivity)]
    simp only [add_comm u t,phase]
  simp_rw [heq]
  rw [dyadicHeightMean_const_mul]
  calc
    _ = (A/(9*N))*((1+A*J/(27*N^2))^q*dyadicHeightMean (fun t =>
        ‖normCoprimeRadialForm S H
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          phase (fun h => norm h/J) (fun a => norm a/N) V (A*J/(27*N^2))‖) T) := by ring
    _ ≤ (A/(9*N))*(K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailPoissonDyadic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the genuine low Poisson annuli for arbitrary coefficients at
the natural Fourier scale. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_poisson_dyadic_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) {R : ℝ} (hR : 1 ≤ R)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (I : Finset ℕ) (β : Eisenstein → ℂ) (Z : ℕ) (A T u N : ℝ),
      1 ≤ (Z:ℝ) → (Z:ℝ)^(1/50:ℝ) ≤ T → 0 < A → 0 < N →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) R) →
      (∀ j ∈ I, 16*(2:ℝ)^j ≤ (Z:ℝ)^(19/20:ℝ)) →
      (∀ j, H j ⊆ frequencyDyad j) →
      dyadicHeightMean (fun t => ‖∑ j ∈ I, finitePoissonContribution S (H j) β (u+t) V A‖) T ≤
        K*(A/N)*(Z:ℝ)^(1-1/40000:ℝ)*(A/(27*N^2))^(-(1/3:ℝ))*
          ∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_poisson_annulus_height_power hMV hC hHuxley hR V hV hV' 3
  let D := SevenEighths.CubicDyadicDecay.decayConstant (1/3)
  have hD : 0 < D := SevenEighths.CubicDyadicDecay.decayConstant_pos _ (by norm_num) (by norm_num)
  refine ⟨K*(2:ℝ)^(1/3:ℝ)*D,by positivity,?_⟩
  intro S H I β Z A T u N hZ hT hA hN hS hrange hI hH
  have hTp : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hT
  let t := A/(27*N^2)
  let C₀ := K*(A/N)*(Z:ℝ)^(1-1/40000:ℝ)*(2:ℝ)^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2
  let F := fun j v => finitePoissonContribution S (H j) β (u+v) V A
  have ht : 0 < t := by dsimp [t]; positivity
  have hrow (j : ℕ) (hj : j ∈ I) :
      dyadicHeightMean (fun v => ‖F j v‖) T ≤ C₀*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := by
    have hJ : 0 < (2:ℝ)^j := by positivity
    have hJ₁ : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hb := hbound S (H j) β Z A (2*(2:ℝ)^j) T u N ((2:ℝ)^j)
      hZ (by linarith) hT hA hN hJ hS hrange
      (by linarith [hI j hj])
      (fun h hh => ⟨(mem_frequencyDyad.mp (hH j hh)).1,(frequencyDyad_norm (hH j hh)).2⟩)
      (fun h hh => ⟨(frequencyDyad_norm (hH j hh)).1,(frequencyDyad_norm (hH j hh)).2⟩)
    have heq : A*(2:ℝ)^j/(27*N^2) = t*2^j := by dsimp [t]; ring
    rw [heq,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hJ.le] at hb
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+t*(2:ℝ)^j) 3)).mpr
    dsimp only [C₀,F]
    first | (convert hb using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hb.trans (le_of_eq (by ring)))
  have hs := averaged_cubic_dyadic_sum I F
    (fun j _ => (finitePoissonContribution_continuous_height S (H j) β V A).comp
      (continuous_const.add continuous_id)) (by dsimp [C₀]; positivity) ht hTp hrow
  apply hs.trans_eq
  dsimp [C₀,t,D]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailPoissonCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete dyadic cutoff lying inside the small-conductor range,
with a fixed power gap past the natural small-B Poisson scale. -/
noncomputable section
namespace CubicFirstMoment

lemma primeGroupTail_poisson_cutoff {Z : ℝ} (_hZ : 0 < Z) (hlarge : 16 ≤ Z^(19/20:ℝ)) :
    ∃ n : ℕ, Z^(19/20:ℝ)/32 ≤ (2:ℝ)^n ∧
      ∀ j : ℕ, j < n → 16*(2:ℝ)^j ≤ Z^(19/20:ℝ) := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near
    ((le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mpr (by simpa using hlarge))
    (by norm_num : (1:ℝ) < 2)
  refine ⟨n,?_,?_⟩
  · have hh := (div_lt_iff₀ (by norm_num : (0:ℝ) < 16)).mp hn'
    rw [pow_succ] at hh
    linarith
  · intro j hj
    have hp : (2:ℝ)^j ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hj.le
    have hn := (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mp hn
    nlinarith

lemma primeGroupTail_poisson_cutoff_scale {Z A J : ℝ} (hZ : 1 ≤ Z)
    (hA : Z^(27/25:ℝ) ≤ A) (hJ : Z^(19/20:ℝ)/32 ≤ J) :
    1/(864*Z^2) ≤ A/(27*Z^2) ∧
      Z^(3/100:ℝ)/864 ≤ (A/(27*Z^2))*J := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have ha : 1 ≤ A := (Real.one_le_rpow hZ (by norm_num)).trans hA
  constructor
  · apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 864*Z^2)
      (by positivity : (0:ℝ) < 27*Z^2)).mpr
    nlinarith [sq_pos_of_pos hz]
  · have hmul := mul_le_mul hA hJ (by positivity : 0 ≤ Z^(19/20:ℝ)/32)
      (zero_le_one.trans ha)
    have hid : Z^(27/25:ℝ)*Z^(19/20:ℝ) = Z^(3/100:ℝ)*Z^2 := by
      rw [← Real.rpow_natCast Z 2,← Real.rpow_add hz,← Real.rpow_add hz]
      norm_num
    have hp : Z^(3/100:ℝ)*Z^2 ≤ 32*(A*J) := by
      rw [← mul_div_assoc,hid] at hmul
      linarith
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 864)).mpr
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hz)).mp
    calc
      _ = Z^(3/100:ℝ)*Z^2 := mul_comm _ _
      _ ≤ 32*(A*J) := hp
      _ = Z^2*((A/(27*Z^2))*J*864) := by field_simp; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailPoissonTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-frequency estimate improves as the outer length grows.
Retaining its inverse powers removes the artificial upper bound on A. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma primeGroupTail_unbounded_tail_scale {Z A J : ℝ} (hZ : 1 ≤ Z)
    (hA : Z^(27/25:ℝ) ≤ A) (hJ : Z^(19/20:ℝ)/32 ≤ J) :
    let t := A/(27*Z^2)
    A*Z*t^(-3:ℝ)/(t*J)^240 ≤ (864:ℝ)^243*Z^(-2:ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have ha : 0 < A := (Real.rpow_pos_of_pos hz _).trans_le hA
  let t := A/(27*Z^2)
  change A*Z*t^(-3:ℝ)/(t*J)^240 ≤ _
  have ht : 0 < t := by dsimp [t]; positivity
  have hj : 0 < J := (div_pos (Real.rpow_pos_of_pos hz _) (by norm_num)).trans_le hJ
  have hcut : Z^(3/100:ℝ)/864 ≤ t*J := (primeGroupTail_poisson_cutoff_scale hZ hA hJ).2
  have ha2 : Z^2 ≤ A^2 := by
    apply pow_le_pow_left₀ hz.le
    exact (show Z ≤ Z^(27/25:ℝ) by
      nth_rw 1 [← Real.rpow_one Z]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)).trans hA
  have hfirst : A*Z*t^(-3:ℝ) ≤ (864:ℝ)^3*Z^5 := by
    have he : A*Z*t^(-3:ℝ) = (27:ℝ)^3*Z^7/A^2 := by
      rw [Real.rpow_neg ht.le,Real.rpow_ofNat]
      dsimp [t]
      field_simp
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    have hm := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ (27:ℝ)^3*Z^5 by positivity)
    have hc : (27:ℝ)^3*Z^5*A^2 ≤ (864:ℝ)^3*Z^5*A^2 := by gcongr; norm_num
    apply (le_trans ?_ hm).trans hc
    ring_nf
    rfl
  have hinv : (t*J)⁻¹ ≤ 864/Z^(3/100:ℝ) := by
    rw [← one_div,div_le_iff₀ (mul_pos ht hj),div_mul_eq_mul_div]
    have hh := (div_le_iff₀ (by norm_num : (0:ℝ) < 864)).mp hcut
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mpr
    nlinarith
  have hpower : ((t*J)^240)⁻¹ ≤ (864:ℝ)^240*Z^(-36/5:ℝ) := by
    rw [← inv_pow]
    apply (pow_le_pow_left₀ (by positivity) hinv 240).trans_eq
    rw [div_pow,← Real.rpow_mul_natCast hz.le]
    rw [show (3/100:ℝ)*(240:ℕ) = 36/5 by norm_num,
      show (-36/5:ℝ) = -(36/5) by ring,Real.rpow_neg hz.le,div_eq_mul_inv]
  calc
    _ ≤ ((864:ℝ)^3*Z^5)*((864:ℝ)^240*Z^(-36/5:ℝ)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hfirst hpower (by positivity) (by positivity)
    _ = (864:ℝ)^243*Z^(-11/5:ℝ) := by
      have he : Z^5*Z^(-36/5:ℝ) = Z^(-11/5:ℝ) := by
        rw [← Real.rpow_natCast Z 5,← Real.rpow_add hz]
        norm_num
      calc
        _ = ((864:ℝ)^3*864^240)*(Z^5*Z^(-36/5:ℝ)) := by ring
        _ = ((864:ℝ)^3*864^240)*Z^(-11/5:ℝ) := by rw [he]
        _ = _ := by rw [←pow_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)) (by positivity)

theorem primeGroupTail_poisson_tail_power (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ),
      1 ≤ N → N ≤ Z → Z^(27/25:ℝ) ≤ A → Z^(19/20:ℝ)/32 ≤ (2:ℝ)^n →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ frequencyDyad j) →
      Summable (fun j => finitePoissonContribution S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution S (H (j+n)) β u V A‖ ≤
        K*Z^(-2:ℝ)*∑ a ∈ S, ‖β a‖^2 := by
  obtain ⟨K,hK,hbound⟩ := arbitrary_poisson_energy_tail V hV hV' 240
  refine ⟨2*K*(864:ℝ)^243,by positivity,?_⟩
  intro S H β A N Z u n hN hNZ hAlo hcut hS hH
  have hZ : 1 ≤ Z := hN.trans hNZ
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hA : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hAlo
  let t := A/(27*Z^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hb := hbound S H β A N Z u n hA hNp hNZ hS hH
  refine ⟨hb.1,?_⟩
  have hp := primeGroupTail_unbounded_tail_scale hZ hAlo hcut
  have hgeo : ((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹ ≤ 2 := by
    norm_num
    have hh : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  calc
    _ ≤ (K*(A/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^240)*(t^(-3:ℝ)*2) :=
      hb.2.trans (mul_le_mul_of_nonneg_left
        (by nlinarith [mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg ht.le (-3))])
        (by positivity))
    _ = (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*(A*Z*t^(-3:ℝ)/(t*(2:ℝ)^n)^240) := by ring
    _ ≤ (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*((864:ℝ)^243*Z^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (2*K)*(∑ a ∈ S, ‖β a‖^2)*((864:ℝ)^243*Z^(-2:ℝ)) := by
      gcongr
      exact div_le_self (by positivity) hN
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailPoissonTotal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete nonzero Poisson series for arbitrary dyadic squarefree
coefficients in the small-B range, including its actual infinite tail. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_poisson_total_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z : ℕ) (A T u : ℝ),
      4 ≤ (Z:ℝ) → 16 ≤ (Z:ℝ)^(19/20:ℝ) → (Z:ℝ)^(1/50:ℝ) ≤ T →
      (Z:ℝ)^(27/25:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ (Z:ℝ)/2 ≤ norm b ∧ norm b ≤ (Z:ℝ)) →
      (∀ j, H j ⊆ frequencyDyad j) →
      dyadicHeightMean (fun t => ‖∑' j : ℕ, finitePoissonContribution S (H j) β (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K₁,hK₁,hshort⟩ := primeGroupTail_poisson_dyadic_height_power hMV hC hHuxley
    (by norm_num : (1:ℝ) ≤ 2) V hV hV'
  obtain ⟨K₂,hK₂,htail⟩ := primeGroupTail_poisson_tail_power V hV hV'
  obtain ⟨K₀,hK₀,henv⟩ := arbitrary_poisson_dyad_energy V hV hV' 3
  refine ⟨K₁*(3*(2:ℝ)^(1/3:ℝ))+2*K₂,by positivity,?_⟩
  intro S H β Z A T u hZ₄ hlarge hT hAlo hS hH
  have hZ : 1 ≤ (Z:ℝ) := by linarith
  have hZp : 0 < (Z:ℝ) := by linarith
  have hN : 0 < (Z:ℝ)/2 := by positivity
  have hN₁ : 1 ≤ (Z:ℝ)/2 := by linarith
  have hNZ : (Z:ℝ)/2 ≤ (Z:ℝ) := by linarith
  have hA : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hAlo
  have hA₁ : 1 ≤ A := (Real.one_le_rpow hZ (by norm_num)).trans hAlo
  have hTp : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  have hp : ∀ b ∈ S, primary b ∧ (Z:ℝ)/2 ≤ norm b ∧ norm b ≤ (Z:ℝ) :=
    fun b hb => ⟨(hS b hb).1,(hS b hb).2.2⟩
  have hrange : ∀ b ∈ S, norm b/((Z:ℝ)/2) ∈ Set.Icc (1:ℝ) 2 := by
    intro b hb
    exact ⟨(le_div_iff₀ hN).mpr (by simpa using (hp b hb).2.1),
      (div_le_iff₀ hN).mpr (by nlinarith [(hp b hb).2.2])⟩
  obtain ⟨n,hn,hprefix⟩ := primeGroupTail_poisson_cutoff hZp hlarge
  let F := fun j v => finitePoissonContribution S (H j) β (u+v) V A
  let t := A/(27*(Z:ℝ)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have htotal : Continuous (fun v => ∑' j : ℕ, F j v) :=
    continuous_poisson_series S H β V A u
      (C := K₀*(A/((Z:ℝ)/2))*(Z:ℝ)*∑ b ∈ S, ‖β b‖^2) ht (fun j v => by
        convert henv S (H j) β A ((Z:ℝ)/2) (Z:ℝ) (u+v) j hA hN hNZ hp (hH j) using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [t]
        ring)
  have hpre := hshort S H (Finset.range n) β Z A T u ((Z:ℝ)/2) hZ hT hA hN
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.2⟩)
    hrange (fun j hj => hprefix j (Finset.mem_range.mp hj)) hH
  have hpre' : dyadicHeightMean (fun v => ‖∑ j ∈ Finset.range n, F j v‖) T ≤
      (K₁*(3*(2:ℝ)^(1/3:ℝ)))*A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    apply hpre.trans_eq
    calc
      _ = K₁*((A/((Z:ℝ)/2))*(Z:ℝ)^(1-1/40000:ℝ)*
          (A/(27*((Z:ℝ)/2)^2))^(-(1/3:ℝ)))*(∑ b ∈ S, ‖β b‖^2) := by ring
      _ = _ := by rw [smallB_dyadic_poisson_scale hA hZp]; ring
  have hpoint (v : ℝ) : ‖∑' j : ℕ, F j v‖ ≤
      ‖∑ j ∈ Finset.range n, F j v‖+K₂*(Z:ℝ)^(-2:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    obtain ⟨hfs,hft⟩ := htail S H β A ((Z:ℝ)/2) (Z:ℝ) (u+v) n hN₁ hNZ hAlo hn hp hH
    exact norm_tsum_prefix_tail n hfs le_rfl hft
  have hfc (j : ℕ) : Continuous (F j) :=
    (finitePoissonContribution_continuous_height S (H j) β V A).comp
      (show Continuous (fun v : ℝ => u+v) from continuous_const.add continuous_id)
  have hsumc : Continuous (fun v => ∑ j ∈ Finset.range n, F j v) :=
    continuous_finsetSum (Finset.range n) (fun j _ => hfc j)
  have hm := dyadicHeightMean_mono htotal.norm (hsumc.norm.add continuous_const) hTp
    (fun v _ => hpoint v)
  change dyadicHeightMean _ T ≤ dyadicHeightMean (fun v =>
    ‖∑ j ∈ Finset.range n, F j v‖+K₂*(Z:ℝ)^(-2:ℝ)*∑ b ∈ S, ‖β b‖^2) T at hm
  rw [dyadicHeightMean_add hsumc.norm continuous_const,dyadicHeightMean_const _ hTp.ne'] at hm
  have hdecay : (Z:ℝ)^(-2:ℝ) ≤ A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ) := by
    apply (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : (-2:ℝ) ≤ 2/3-1/40000)).trans
    exact le_mul_of_one_le_left (Real.rpow_nonneg hZp.le _)
      (Real.one_le_rpow hA₁ (by norm_num))
  apply hm.trans
  calc
    _ ≤ (K₁*(3*(2:ℝ)^(1/3:ℝ)))*A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖β b‖^2+
        2*(K₂*(A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ))*∑ b ∈ S, ‖β b‖^2) := by
      exact add_le_add hpre' (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay hK₂.le)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by norm_num))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailCoprimeDispersion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arbitrary-coefficient small-B estimate for the original
coprime dispersion Gram form, obtained from the complete Poisson series. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_coprime_dispersion_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (A T u : ℝ), 4 ≤ (Z:ℝ) → 16 ≤ (Z:ℝ)^(19/20:ℝ) →
      (Z:ℝ)^(1/50:ℝ) ≤ T → (Z:ℝ)^(27/25:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ (Z:ℝ)/2 ≤ norm b ∧ norm b ≤ (Z:ℝ)) →
      dyadicHeightMean (fun t => ‖coprimeDispersionGram S β (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_poisson_total_height_power hMV hC hHuxley V hV hV'
  refine ⟨K,hK,?_⟩
  intro S β Z A T u hZ hlarge hT hAlo hS
  have hA : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < (Z:ℝ)) _).trans_le hAlo
  have hp : ∀ b ∈ S, primary b ∧ Squarefree b ∧ b ≠ 1 := by
    intro b hb
    refine ⟨(hS b hb).1,(hS b hb).2.1,?_⟩
    intro he
    have hn := (hS b hb).2.2.1
    rw [he,norm_one_eq] at hn
    linarith
  have he (t : ℝ) := coprimeDispersionGram_eq_poisson_series S hp β (u+t) V hV hV' hA
  simp_rw [he]
  exact hbound S frequencyDyad β Z A T u hZ hlarge hT hAlo hS (fun _ => Finset.Subset.refl _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailRealLength
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer norms permit an exact floor cutoff after division by a
common factor. No rounding error is added to the coefficient support. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_coprime_height_real
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (Z A T u : ℝ), 4 ≤ (⌊Z⌋₊:ℝ) → 16 ≤ (⌊Z⌋₊:ℝ)^(3/4:ℝ) →
      Z^(1/50:ℝ) ≤ T → Z^(27/25:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖coprimeGramForm S (fun b => v b*star (normTwist (u+t) b)) V A‖) T ≤
        K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖v b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_coprime_dispersion_height_power hMV hC hHuxley V hV hV'
  refine ⟨K,hK,?_⟩
  intro S v Z A T u hZ hlarge hT hA hS
  have hZ₀ : 0 ≤ Z := by
    by_contra h
    have hf : ⌊Z⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge h)
    simp only [hf,Nat.cast_zero] at hZ
    linarith
  have hf : (⌊Z⌋₊:ℝ) ≤ Z := Nat.floor_le hZ₀
  have hA₀ : 0 ≤ A := (Real.rpow_nonneg hZ₀ _).trans hA
  have hS' : ∀ b ∈ S, primary b ∧ Squarefree b ∧
      (⌊Z⌋₊:ℝ)/2 ≤ norm b ∧ norm b ≤ (⌊Z⌋₊:ℝ) := by
    intro b hb
    refine ⟨(hS b hb).1,(hS b hb).2.1,?_,?_⟩
    · linarith [(hS b hb).2.2.1]
    · have hh : normNat b ≤ ⌊Z⌋₊ := Nat.le_floor (by
        rw [normNat_cast]
        exact (hS b hb).2.2.2)
      have hr : (normNat b : ℝ) ≤ (⌊Z⌋₊:ℝ) := by exact_mod_cast hh
      rwa [normNat_cast] at hr
  have hlarge' : 16 ≤ (⌊Z⌋₊:ℝ)^(19/20:ℝ) := hlarge.trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ (⌊Z⌋₊:ℝ)) (by norm_num))
  have hh := hbound S (gramUntwist v) ⌊Z⌋₊ A T u hZ hlarge' 
    ((Real.rpow_le_rpow (by positivity) hf (by norm_num)).trans hT)
    ((Real.rpow_le_rpow (by positivity) hf (by norm_num)).trans hA) hS'
  have he (t : ℝ) := coprimeGramForm_height_eq S
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) v (u+t) V A
  simp_rw [← he] at hh
  have henergy : (∑ b ∈ S, ‖gramUntwist v b‖^2) = ∑ b ∈ S, ‖v b‖^2 := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [gramUntwist_norm (hS b hb).1 (hS b hb).2.1]
  rw [henergy] at hh
  exact hh.trans (by
    gcongr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailCommonScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small-B scale remains valid after the exact common-factor and
Möbius changes of variables. -/
noncomputable section
namespace CubicFirstMoment

lemma primeGroupTail_common_outer_scale {Z A k m : ℝ} (hZ : 0 ≤ Z)
    (hk : 1 ≤ k) (hm : 0 < m) (hmk : m ≤ k) (hA : Z^(27/25:ℝ) ≤ A) :
    (Z/k)^(27/25:ℝ) ≤ A/m := by
  have hkp : 0 < k := zero_lt_one.trans_le hk
  have hkpw : k ≤ k^(27/25:ℝ) := by
    calc
      k = k^(1:ℝ) := (Real.rpow_one k).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk (by norm_num)
  rw [Real.div_rpow hZ hkp.le]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hZ _) hm (hmk.trans hkpw)).trans
    (div_le_div_of_nonneg_right hA hm.le)

lemma primeGroupTail_common_height_scale {Z T k : ℝ} (hZ : 0 ≤ Z) (hk : 1 ≤ k)
    (hT : Z^(1/50:ℝ) ≤ T) : (Z/k)^(1/50:ℝ) ≤ T := by
  exact (Real.rpow_le_rpow (by positivity)
    (div_le_self hZ hk) (by norm_num)).trans hT

lemma primeGroupTail_common_bound_scale {Z A k m : ℝ} (hZ : 0 ≤ Z) (hA : 0 ≤ A)
    (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (A/m)^(2/3:ℝ)*(Z/k)^(2/3-1/40000:ℝ) ≤
      A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ) := by
  exact mul_le_mul
    (Real.rpow_le_rpow (by positivity) (div_le_self hA hm) (by norm_num))
    (Real.rpow_le_rpow (by positivity) (div_le_self hZ hk) (by norm_num))
    (by positivity) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailCommonRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Möbius summand of a shared-factor row inherits the
arbitrary-coefficient height saving, with the original row energy. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_common_row_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ) (k m : Eisenstein), 0 ≤ Z → Z^(27/25:ℝ) ≤ A →
      Z^(1/50:ℝ) ≤ T → primary k → primary m → m ∣ k →
      4 ≤ (⌊Z/norm k⌋₊:ℝ) → 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖coprimeGramForm (residualRows S k)
        (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k m)
        V (A/norm m)‖) T ≤
      K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*commonBlockEnergy S β k := by
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_coprime_height_real hMV hC hHuxley V hV hV'
  refine ⟨K,hK,?_⟩
  intro S β Z A T u k m hZ hA hT hk hm hmk hfloor hlarge hS
  have hk₀ := primary_ne_zero hk
  have hk₁ := one_le_norm hk₀
  have hm₀ := primary_ne_zero hm
  have hm₁ := one_le_norm hm₀
  have hmkN := norm_le_of_dvd hk₀ hmk
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  have hr := residualRows_primary hk hS₀
  let v := commonBlockCoefficient (fun b => star (β b*gauss b)) k m
  have hrows : ∀ b ∈ residualRows S k,
      primary b ∧ Squarefree b ∧ (Z/norm k)/2 ≤ norm b ∧ norm b ≤ Z/norm k := by
    intro b hb
    have hkb := hS (k*b) ((mem_residualRows hk₀).mp hb)
    refine ⟨(hr b hb).1,(hr b hb).2,?_,?_⟩
    · rw [div_right_comm]
      apply (div_le_iff₀ (norm_pos_of_ne_zero hk₀)).mpr
      rw [norm_mul_eq] at hkb
      nlinarith [hkb.2.2.1]
    · apply (le_div_iff₀ (norm_pos_of_ne_zero hk₀)).mpr
      simpa only [norm_mul_eq,mul_comm] using hkb.2.2.2
  have hrow := hbound (residualRows S k) v (Z/norm k) (A/norm m) T u hfloor hlarge
    (primeGroupTail_common_height_scale hZ hk₁ hT)
    (primeGroupTail_common_outer_scale hZ hk₁ (norm_pos_of_ne_zero hm₀) hmkN hA) hrows
  have he (t : ℝ) : coprimeGramForm (residualRows S k)
      (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k m) V (A/norm m) =
      coprimeGramForm (residualRows S k) (fun b => v b*star (normTwist (u+t) b)) V (A/norm m) := by
    rw [common_coprime_height_eq S β k m hk hS₀,
      ← coprimeGramForm_height_eq _ hr]
  simp_rw [he]
  have henergy : (∑ b ∈ residualRows S k, ‖v b‖^2) ≤ commonBlockEnergy S β k := by
    apply (commonBlockCoefficient_unweighted_energy_le S hS₀
      (fun b => star (β b*gauss b)) hk m).trans
    unfold commonBlockEnergy
    apply Finset.sum_le_sum
    intro b hb
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hkb := (hS (k*b) ((mem_residualRows hk₀).mp hb)).1
    apply pow_le_pow_left₀ (by positivity)
    simp only [norm_star,norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_gauss_le_one hkb)
  have hA₀ : 0 ≤ A := (Real.rpow_nonneg hZ _).trans hA
  exact hrow.trans (by
    have hs := primeGroupTail_common_bound_scale hZ hA₀ hk₁ hm₁
    calc
      _ ≤ K*(A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ))*(∑ b ∈ residualRows S k, ‖v b‖^2) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs hK.le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      _ ≤ _ := by
        have hsc : 0 ≤ K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ) := by positivity
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henergy hsc)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailCommonBlock
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore every Möbius divisor in a small common-factor block. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_common_block_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ) (k : Eisenstein), 0 < Z → Z^(27/25:ℝ) ≤ A →
      Z^(1/50:ℝ) ≤ T → primary k → Squarefree k →
      4 ≤ (⌊Z/norm k⌋₊:ℝ) → 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) V A k‖) T ≤
      K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*
        ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) := by
  obtain ⟨K,hK,hrow⟩ := primeGroupTail_common_row_height_power hMV hC hHuxley V hV hV'
  refine ⟨K,hK,?_⟩
  intro S β Z A T u k hZ hA hT hk hsk hfloor hlarge hS
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZ _).trans_le hA
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos hZ _).trans_le hT
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  let P := (primaryPrimeFactors k).powerset
  let F (s : Finset Eisenstein) (t : ℝ) :=
    coprimeGramForm (residualRows S k)
      (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k (∏ p ∈ s,p))
      V (A/norm (∏ p ∈ s,p))
  have hfc (s : Finset Eisenstein) : Continuous (F s) := by
    have he (t : ℝ) := common_coprime_height_eq S β k (∏ p ∈ s,p) hk hS₀ (u+t) V
      (A/norm (∏ p ∈ s,p))
    simp_rw [F,he]
    exact (continuous_coprimeDispersionGram _ _ V _).comp
      (show Continuous (fun t : ℝ => u+t) from continuous_const.add continuous_id)
  have he (t : ℝ) : commonGramBlock S
      (fun b => star (dispersionAmplitude β (u+t) b)) V A k =
      ∑ s ∈ P, (idealMoebius (∏ p ∈ s,p):ℂ)*F s t :=
    commonGramBlock_moebius S hS₀ _ V hV hV' hA₀ hk hsk
  simp_rw [he]
  apply (dyadicHeightMean_norm_sum_le P
    (fun s t => (idealMoebius (∏ p ∈ s,p):ℂ)*F s t)
    (fun s _ => continuous_const.mul (hfc s)) hT₀).trans
  have hb (s : Finset Eisenstein) (hs : s ∈ P) :
      dyadicHeightMean (fun t => ‖(idealMoebius (∏ p ∈ s,p):ℂ)*F s t‖) T ≤
        K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*commonBlockEnergy S β k := by
    have hsub : s ⊆ primaryPrimeFactors k := Finset.mem_powerset.mp hs
    have hm : primary (∏ p ∈ s,p) := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).1.1)
    have hmk : (∏ p ∈ s,p) ∣ k := (primary_subsets_prod_dvd hk hsub k).mpr
      (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).2)
    have hmc : Continuous (fun t => (idealMoebius (∏ p ∈ s,p):ℂ)*F s t) :=
      continuous_const.mul (hfc s)
    have havg := dyadicHeightMean_mono
      (f := fun t => ‖(idealMoebius (∏ p ∈ s,p):ℂ)*F s t‖)
      (g := fun t => ‖F s t‖) hmc.norm (hfc s).norm hT₀ (fun t _ => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _))
    exact havg.trans (hrow S β Z A T u k _ hZ.le hA hT hk
      hm
      hmk hfloor hlarge hS)
  exact (Finset.sum_le_sum hb).trans_eq (by
    simp only [P,Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBCommonSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the actual small-common-factor blocks with their joint divisor
energy. The loss is smaller than the height saving. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma continuous_commonGramBlock_height (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (k : Eisenstein) (V : ℝ → ℂ) (A u : ℝ) :
    Continuous (fun t => commonGramBlock S
      (fun b => star (dispersionAmplitude β (u+t) b)) V A k) := by
  unfold commonGramBlock
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact ((((continuous_dispersionAmplitude β (k*a)).comp
      (continuous_const.add continuous_id)).star).mul
      ((((continuous_dispersionAmplitude β (k*b)).comp
      (continuous_const.add continuous_id)).star).star)).mul continuous_const
  · exact continuous_const

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailCommonSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum all small common factors at the enlarged conductor cutoff. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeGroupTail_common_sum_height_power_oai
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S I : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ), 0 < Z → Z^(27/25:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      I ⊆ commonRowFactors S →
      (∀ k ∈ I, 4 ≤ (⌊Z/norm k⌋₊:ℝ) ∧ 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖∑ k ∈ I, commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) V A k‖) T ≤
      K*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hblock⟩ := primeGroupTail_common_block_height_power hMV hC hHuxley V hV hV'
  obtain ⟨E,hE,henergy⟩ := common_energy_small_power (1/80000) (by norm_num)
  refine ⟨K*E,by positivity,?_⟩
  intro S I β Z A T u hZ hA hT hI hfloor hS
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZ _).trans_le hA
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos hZ _).trans_le hT
  have hsum := dyadicHeightMean_norm_sum_le I
    (fun k t => commonGramBlock S (fun b => star (dispersionAmplitude β (u+t) b)) V A k)
    (fun k _ => continuous_commonGramBlock_height S β k V A u) hT₀
  have hb (k : Eisenstein) (hk : k ∈ I) := hblock S β Z A T u k hZ hA hT
    (commonRowFactors_spec hS₀ (hI hk)).1 (commonRowFactors_spec hS₀ (hI hk)).2
    (hfloor k hk).1 (hfloor k hk).2 hS
  have hbound : (∑ k ∈ I, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) ≤
      E*Z^(1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    apply le_trans _ (henergy S β Z (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.2⟩))
    exact Finset.sum_le_sum_of_subset_of_nonneg hI (fun k hk _ => by
      exact mul_nonneg (by positivity) (commonBlockEnergy_nonneg S β k))
  calc
    _ ≤ ∑ k ∈ I, K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*
        ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) :=
      hsum.trans (Finset.sum_le_sum hb)
    _ = (K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ))*
        (∑ k ∈ I, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) := by
      rw [Finset.mul_sum]
    _ ≤ (K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ))*(E*Z^(1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      have he : Z^(2/3-1/40000:ℝ)*Z^(1/80000:ℝ) = Z^(2/3-1/80000:ℝ) := by
        rw [← Real.rpow_add hZ]
        congr 1
        norm_num
      calc
        _ = (K*E)*A^(2/3:ℝ)*(Z^(2/3-1/40000:ℝ)*Z^(1/80000:ℝ))*∑ b ∈ S, ‖β b‖^2 := by ring
        _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.primeGroupTail_common_sum_height_power_oai := @OAI.CubicFirstMoment.primeGroupTail_common_sum_height_power_oai
