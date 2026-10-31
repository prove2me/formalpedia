-- Prove2me | solution 1 for OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:37:57.243917+00:00
-- url     : https://prove2.me/submissions/b0e92e2f-36c7-449b-93d4-f89b4fc3c1a0

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022
import Theorems.Thm_OAI_CubicFirstMoment_outer_core_block_sieve

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma finiteCubicBound_nonneg (S H : Finset Eisenstein) : 0 ≤ finiteCubicBound S H :=
  sq_nonneg _

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

lemma coefficientVector_norm_sq (S : Finset Eisenstein) (u : Eisenstein → ℂ) :
    ‖(WithLp.toLp 2 (fun a : S => u a.val) : EuclideanSpace ℂ S)‖^2 =
      ∑ a ∈ S, ‖u a‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact (Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => ‖u a‖^2)).symm

lemma finiteCubicOperator_norm_sq (S H : Finset Eisenstein) (u : Eisenstein → ℂ) :
    ‖finiteCubicOperator S H (WithLp.toLp 2 (fun a : S => u a.val))‖^2 =
      ∑ h ∈ H, ‖∑ a ∈ S, u a * cubicSymbol a h‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ h : H, ‖finiteCubicOperator S H (WithLp.toLp 2 (fun a : S => u a.val)) h‖^2) = _
  simp_rw [finiteCubicOperator_apply]
  exact (Finset.sum_subtype H (fun _ => Iff.rfl)
    (fun h => ‖∑ a ∈ S, u a * cubicSymbol a h‖^2)).symm

lemma finiteCubicBound_le_iff (S H : Finset Eisenstein) {C : ℝ} (hC : 0 ≤ C) :
    finiteCubicBound S H ≤ C ↔ ∀ u : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ a ∈ S, u a * cubicSymbol a h‖^2) ≤
        C * ∑ a ∈ S, ‖u a‖^2 := by
  constructor
  · intro h u
    exact (finiteCubicBound_controls_mass S H u).trans
      (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  · intro h
    have hn : ‖finiteCubicOperator S H‖ ≤ Real.sqrt C := by
      apply (ContinuousLinearMap.opNorm_le_iff (f := finiteCubicOperator S H)
        (Real.sqrt_nonneg C)).mpr
      intro v
      let u (a : Eisenstein) : ℂ := if ha : a ∈ S then v ⟨a, ha⟩ else 0
      have hv : WithLp.toLp 2 (fun a : S => u a.val) = v := by
        apply PiLp.ext
        intro a
        simp [u]
      have hh : ‖finiteCubicOperator S H v‖^2 ≤ C*‖v‖^2 := by
        rw [← hv, finiteCubicOperator_norm_sq, coefficientVector_norm_sq]
        exact h u
      apply (sq_le_sq₀ (_root_.norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (_root_.norm_nonneg _))).mp
      simpa only [mul_pow, Real.sq_sqrt hC] using hh
    exact (pow_le_pow_left₀ (_root_.norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hC)

end CubicFirstMoment

namespace CubicFirstMoment

lemma finiteCubicBound_mono {S T H J : Finset Eisenstein} (hST : S ⊆ T) (hHJ : H ⊆ J) :
    finiteCubicBound S H ≤ finiteCubicBound T J := by
  apply (finiteCubicBound_le_iff S H (finiteCubicBound_nonneg T J)).mpr
  intro u
  let v (a : Eisenstein) := if a ∈ S then u a else 0
  have hi (h : Eisenstein) : (∑ a ∈ T, v a * cubicSymbol a h) =
      ∑ a ∈ S, u a * cubicSymbol a h := by
    calc
      _ = ∑ a ∈ S, v a * cubicSymbol a h :=
        (Finset.sum_subset hST (fun a _ ha => by simp [v, ha])).symm
      _ = _ := Finset.sum_congr rfl (fun a ha => by simp [v, ha])
  have hv : (∑ a ∈ T, ‖v a‖^2) = ∑ a ∈ S, ‖u a‖^2 := by
    calc
      _ = ∑ a ∈ S, ‖v a‖^2 :=
        (Finset.sum_subset hST (fun a _ ha => by simp [v, ha])).symm
      _ = _ := Finset.sum_congr rfl (fun a ha => by simp [v, ha])
  have hb := finiteCubicBound_controls_mass T J v
  simp_rw [hi, hv] at hb
  exact (Finset.sum_le_sum_of_subset_of_nonneg hHJ (fun _ _ _ => sq_nonneg _)).trans hb

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
-- module Solutions.OAIQ096_CM.CubicGram_MellinNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma coprimeNormMajorant_nonneg (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ) :
    0 ≤ coprimeNormMajorant S H U v w := by
  apply Finset.sum_nonneg
  intro s hs
  apply div_nonneg _ (by norm_num)
  exact mul_nonneg (finiteCubicBound_nonneg _ _) (add_nonneg
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

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
-- module Solutions.OAIQ096_CM.CubicGram_NormRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor-completed energies and the coprime Poisson norm recurrence. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorCompleted_energy_le (S U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (hU : ∀ p ∈ U, primaryPrime p)
    (v : Eisenstein → ℂ) :
    (∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) ≤
      ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖v a‖^2 := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.sum_filter]
  have hs : U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a) ⊆
      (primaryPrimeFactors a).powerset := by
    intro s hs
    obtain ⟨hs,hd⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_powerset.mpr (primeSet_subset_factors_of_prod_dvd (hS a ha)
      (fun p hp => hU p (Finset.mem_powerset.mp hs hp)) hd)
  calc
    _ ≤ ∑ _s ∈ (primaryPrimeFactors a).powerset, ‖v a‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]

lemma coprimeNormMajorant_le_divisorEnergy (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (hU : ∀ p ∈ U, primaryPrime p)
    (v w : Eisenstein → ℂ) :
    coprimeNormMajorant S H U v w ≤ finiteCubicBound S H *
      ((∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖v a‖^2) +
       (∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖w a‖^2)) / 2 := by
  calc
    _ ≤ ∑ s ∈ U.powerset, finiteCubicBound S H *
        ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) +
         (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖^2)) / 2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (finiteCubicBound_mono (Finset.filter_subset _ _) (Finset.Subset.refl _))
        (add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))) (by norm_num)
    _ = finiteCubicBound S H *
        ((∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) +
         (∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖^2)) / 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add (divisorCompleted_energy_le S U hS hU v)
        (divisorCompleted_energy_le S U hS hU w)) (finiteCubicBound_nonneg _ _)) (by norm_num)

lemma sievePrimeSet_primary (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a) :
    ∀ p ∈ sievePrimeSet S, primaryPrime p := by
  intro p hp
  obtain ⟨a,ha,hp⟩ := Finset.mem_biUnion.mp hp
  exact (primaryPrimeFactor_spec (hS a ha) hp).1

lemma factors_subset_sievePrimeSet {S : Finset Eisenstein} {a : Eisenstein} (ha : a ∈ S) :
    primaryPrimeFactors a ⊆ sievePrimeSet S := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨a,ha,hp⟩

end CubicFirstMoment

namespace CubicFirstMoment

lemma gaussRowCoefficient_norm_sq {a : Eisenstein} (ha : primary a)
    (hsa : Squarefree a) (u : Eisenstein → ℂ) :
    ‖gaussRowCoefficient u a‖^2 = ‖u a‖^2 / norm a := by
  simp only [gaussRowCoefficient, norm_div, norm_mul, norm_gauss_of_squarefree ha hsa,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt (norm_nonneg _)]

lemma gramDyadTerm_separated (a b h : Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) {Z J N : ℝ} (hZ : 0 ≤ Z) (hJ : J ≠ 0) (hN : N ≠ 0) :
    u a * star (u b) * ((Z / (9*Real.sqrt (norm (a*b))) : ℝ) : ℂ) *
      (gauss a * star (gauss b)) * gramDualTerm a b W Z h =
    ((Z/9 : ℝ) : ℂ) *
      (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
      ((gaussRowCoefficient u a * star (cubicSymbol a h)) *
        star (gaussRowCoefficient u b * star (cubicSymbol b h))) *
      radialDualProfile W ((Z*J/(27*N^2))*(norm h/J)/((norm a/N)*(norm b/N))) := by
  have hn : norm (a*b) = norm a * norm b := Complex.normSq_mul _ _
  have hs := Real.sqrt_mul (norm_nonneg a) (norm b)
  have he : (Z*J/(27*N^2))*(norm h/J)/((norm a/N)*(norm b/N)) =
      Z*norm h/(27*(norm a * norm b)) := by
    field_simp
  rw [gramDualTerm_radial a b W hZ, hn, hs, he]
  have hr (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  simp only [gaussRowCoefficient, star_mul, star_star, star_inv₀, hr,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_inv, div_eq_mul_inv,
    mul_inv_rev]
  ring

lemma coprimePoissonDyad_separated (S H : Finset Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) {Z J N : ℝ} (hZ : 0 ≤ Z) (hJ : J ≠ 0) (hN : N ≠ 0) :
    coprimePoissonDyad S H u W Z = ((Z/9 : ℝ) : ℂ) *
      coprimeRadialForm S H (gaussRowCoefficient u) (gaussRowCoefficient u)
        (fun h => (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ))
        (fun h => norm h/J) (fun a => norm a/N) W (Z*J/(27*N^2)) := by
  unfold coprimePoissonDyad coprimeRadialForm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := H) (t := S)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm (s := H) (t := S)]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    apply Finset.sum_congr rfl
    intro h hh
    rw [gramDyadTerm_separated a b h u W hZ hJ hN]
    ring
  · simp [hab]

end CubicFirstMoment

namespace CubicFirstMoment

lemma gaussRowCoefficient_divisor_energy (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    {N : ℝ} (hN : 0 < N) (hSN : ∀ a ∈ S, N ≤ norm a) :
    (∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖gaussRowCoefficient u a‖^2) ≤
      (∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2) / N := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro a ha
  rw [gaussRowCoefficient_norm_sq (hS a ha).1 (hS a ha).2, ← mul_div_assoc]
  exact div_le_div_of_nonneg_left (by positivity) hN (hSN a ha)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primaryCommonFactor_decomposition {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q) :
    ∃ a b : Eisenstein, primary a ∧ primary b ∧ Squarefree a ∧ Squarefree b ∧
      IsCoprime a b ∧ p = primaryCommonFactor p q*a ∧ q = primaryCommonFactor p q*b := by
  obtain ⟨k,a,b,hk,ha,hb,hsk,hsa,hsb,hab,_,_,hpa,hqb⟩ :=
    primarySquarefree_common_decomposition hp hq hsp hsq
  have he : primaryCommonFactor p q = k := hpa ▸ hqb ▸ primaryCommonFactor_mul hk hsk ha hb hab
  exact ⟨a,b,ha,hb,hsa,hsb,hab,by simpa [he] using hpa,by simpa [he] using hqb⟩

lemma primaryCommonFactor_spec {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q) :
    primary (primaryCommonFactor p q) ∧ Squarefree (primaryCommonFactor p q) ∧
      primaryCommonFactor p q ∣ p ∧ primaryCommonFactor p q ∣ q := by
  obtain ⟨k,a,b,hk,ha,hb,hsk,hsa,hsb,hab,_,_,hpa,hqb⟩ :=
    primarySquarefree_common_decomposition hp hq hsp hsq
  have he : primaryCommonFactor p q = k := hpa ▸ hqb ▸ primaryCommonFactor_mul hk hsk ha hb hab
  rw [he,hpa,hqb]
  exact ⟨hk,hsk,dvd_mul_right k a,dvd_mul_right k b⟩

lemma mem_commonRowFactors {S : Finset Eisenstein} {p q : Eisenstein}
    (hp : p ∈ S) (hq : q ∈ S) : primaryCommonFactor p q ∈ commonRowFactors S :=
  Finset.mem_image.mpr ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,rfl⟩

lemma commonRowFactors_spec {S : Finset Eisenstein}
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) {k : Eisenstein}
    (hk : k ∈ commonRowFactors S) : primary k ∧ Squarefree k := by
  obtain ⟨⟨p,q⟩,hpq,rfl⟩ := Finset.mem_image.mp hk
  have hp := hS p (Finset.mem_product.mp hpq).1
  have hq := hS q (Finset.mem_product.mp hpq).2
  exact ⟨(primaryCommonFactor_spec hp.1 hq.1 hp.2 hq.2).1,
    (primaryCommonFactor_spec hp.1 hq.1 hp.2 hq.2).2.1⟩

lemma residualRows_image {S : Finset Eisenstein} {k : Eisenstein} (hk : k ≠ 0) :
    (residualRows S k).image (k*·) = S.filter (fun p => k ∣ p) := by
  ext p
  simp only [Finset.mem_image,mem_residualRows hk,Finset.mem_filter]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,dvd_mul_right k a⟩
  · rintro ⟨hp,a,rfl⟩
    exact ⟨a,hp,rfl⟩

lemma commonFactor_eq_iff_coprime {k a b : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (hsa : Squarefree (k*a)) (hsb : Squarefree (k*b)) :
    primaryCommonFactor (k*a) (k*b) = k ↔ IsCoprime a b := by
  constructor
  · intro he
    obtain ⟨a',b',_,_,_,_,hab,hpa,hqb⟩ := primaryCommonFactor_decomposition
      (primary_mul hk ha) (primary_mul hk hb) hsa hsb
    rw [he] at hpa hqb
    have hea := mul_left_cancel₀ (primary_ne_zero hk) hpa
    have heb := mul_left_cancel₀ (primary_ne_zero hk) hqb
    simpa only [← hea,← heb] using hab
  · exact primaryCommonFactor_mul hk hsk ha hb

lemma sum_residualRows {S : Finset Eisenstein} {k : Eisenstein} (hk : k ≠ 0)
    (f : Eisenstein → ℂ) :
    (∑ a ∈ residualRows S k, f (k*a)) = ∑ p ∈ S.filter (fun p => k ∣ p), f p := by
  rw [← residualRows_image hk,Finset.sum_image]
  intro a ha b hb he
  exact mul_left_cancel₀ hk he

lemma common_factor_block_reindex (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    {k : Eisenstein} (hk : primary k) (hsk : Squarefree k)
    (F : Eisenstein → Eisenstein → ℂ) :
    (∑ p ∈ S, ∑ q ∈ S, if primaryCommonFactor p q = k then F p q else 0) =
      ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        if IsCoprime a b then F (k*a) (k*b) else 0 := by
  have hn := primary_ne_zero hk
  have hp := residualRows_primary hk hS
  have hrhs : (∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        if IsCoprime a b then F (k*a) (k*b) else 0) =
      ∑ p ∈ S.filter (fun p => k ∣ p), ∑ q ∈ S.filter (fun q => k ∣ q),
        if primaryCommonFactor p q = k then F p q else 0 := by
    calc
      _ = ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
          if primaryCommonFactor (k*a) (k*b) = k then F (k*a) (k*b) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        simp only [commonFactor_eq_iff_coprime hk hsk (hp a ha).1 (hp b hb).1
          (hS (k*a) ((mem_residualRows hn).mp ha)).2
          (hS (k*b) ((mem_residualRows hn).mp hb)).2]
      _ = ∑ a ∈ residualRows S k, ∑ q ∈ S.filter (fun q => k ∣ q),
          if primaryCommonFactor (k*a) q = k then F (k*a) q else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact sum_residualRows (S := S) hn
          (fun q => if primaryCommonFactor (k*a) q = k then F (k*a) q else 0)
      _ = _ := sum_residualRows (S := S) hn
        (fun p => ∑ q ∈ S.filter (fun q => k ∣ q), if primaryCommonFactor p q = k then F p q else 0)
  rw [hrhs]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hpS
  by_cases hpk : k ∣ p
  · simp only [ite_eq_left hpk]
    apply Finset.sum_congr rfl
    intro q hqS
    by_cases hqk : k ∣ q
    · simp [hqk]
    · have he : primaryCommonFactor p q ≠ k := by
        intro he
        exact hqk (he ▸ (primaryCommonFactor_spec (hS p hpS).1 (hS q hqS).1
          (hS p hpS).2 (hS q hqS).2).2.2.2)
      simp [hqk,he]
  · simp only [ite_eq_right hpk]
    apply Finset.sum_eq_zero
    intro q hqS
    have he : primaryCommonFactor p q ≠ k := by
      intro he
      exact hpk (he ▸ (primaryCommonFactor_spec (hS p hpS).1 (hS q hqS).1
        (hS p hpS).2 (hS q hqS).2).2.2.1)
    simp [he]

theorem common_factor_matrix_decomposition (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (F : Eisenstein → Eisenstein → ℂ) :
    (∑ p ∈ S, ∑ q ∈ S, F p q) =
      ∑ k ∈ commonRowFactors S, ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        if IsCoprime a b then F (k*a) (k*b) else 0 := by
  calc
    _ = ∑ p ∈ S, ∑ q ∈ S, ∑ k ∈ commonRowFactors S,
        if primaryCommonFactor p q = k then F p q else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      simp [mem_commonRowFactors hp hq]
    _ = ∑ k ∈ commonRowFactors S, ∑ p ∈ S, ∑ q ∈ S,
        if primaryCommonFactor p q = k then F p q else 0 := by
      simp_rw [Finset.sum_comm (s := S) (t := commonRowFactors S)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact common_factor_block_reindex S hS (commonRowFactors_spec hS hk).1
        (commonRowFactors_spec hS hk).2 F

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cube_decomposition (n : Eisenstein) :
    ∃ s t c : Eisenstein, Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧ n = s*t^2*c^3 := by
  refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
  · exact ⟨1,1,0,squarefree_one,squarefree_one,isCoprime_one_left,by simp⟩
  · intro u hu
    exact ⟨u,1,1,hu.squarefree,squarefree_one,isCoprime_one_right,by simp⟩
  · intro b p hb hp ih
    obtain ⟨s,t,c,hss,hst,hcop,rfl⟩ := ih
    by_cases hps : p ∣ s
    · obtain ⟨s',rfl⟩ := hps
      have hps' : IsCoprime p s' := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hss).1
      have hpt : IsCoprime p t := hcop.of_mul_left_left
      refine ⟨s',p*t,c,hss.of_mul_right,
        squarefree_mul_iff.mpr ⟨hpt.isRelPrime,hp.squarefree,hst⟩,
        hps'.symm.mul_right hcop.of_mul_left_right,?_⟩
      ring
    · by_cases hpt : p ∣ t
      · obtain ⟨t',rfl⟩ := hpt
        refine ⟨s,t',p*c,hss,hst.of_mul_right,hcop.of_mul_right_right,?_⟩
        ring
      · have hps' := hp.coprime_iff_not_dvd.mpr hps
        have hpt' := hp.coprime_iff_not_dvd.mpr hpt
        refine ⟨p*s,t,c,squarefree_mul_iff.mpr ⟨hps'.isRelPrime,hp.squarefree,hss⟩,
          hst,hpt'.mul_left hcop,?_⟩
        ring

theorem squarefree_ramified_split (n : Eisenstein) (hs : Squarefree n) :
    ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
  have h : ∀ n : Eisenstein, Squarefree n →
      ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
    intro n
    refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
    · intro hs
      have hh := hs 0 (by simp)
      exact (not_isUnit_zero hh).elim
    · intro u hu hs
      refine ⟨1,u,one_dvd _,?_,by simp⟩
      exact (isCoprime_zero_right.mpr hu).of_isCoprime_of_dvd_right (dvd_zero 3)
    · intro b p hb hp ih hs
      obtain ⟨d,e,hd,he,hbe⟩ := ih hs.of_mul_right
      have hpb : IsCoprime p b := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
      by_cases hp3 : p ∣ 3
      · have hpd : IsCoprime p d := (hbe ▸ hpb).of_mul_right_left
        refine ⟨p*d,e,hpd.mul_dvd hp3 hd,he,?_⟩
        rw [hbe]; ring
      · refine ⟨d,p*e,hd,(hp.coprime_iff_not_dvd.mpr hp3).mul_left he,?_⟩
        rw [hbe]; ring
  exact h n hs

lemma unit_residue_of_isCoprime_three {e : Eisenstein} (he : IsCoprime e 3) :
    IsUnit (Ideal.Quotient.mk (modulus 3) e) := by
  have h := he.map (Ideal.Quotient.mk (modulus 3))
  simpa only [residue_three_eq_zero, isCoprime_zero_right] using h

lemma norm_le_of_dvd {a b : Eisenstein} (hb : b ≠ 0) (hd : a ∣ b) :
    norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := hd
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg a) (one_le_norm hc)

theorem squarefree_primary_residual (n : Eisenstein) (hs : Squarefree n) :
    ∃ r s : Eisenstein, r ≠ 0 ∧ norm r ≤ 9 ∧ primary s ∧ Squarefree s ∧ n = r*s := by
  obtain ⟨d,e,hd,he,hde⟩ := squarefree_ramified_split n hs
  obtain ⟨u,hu,hprim⟩ := unit_lift_mod_three (unit_residue_of_isCoprime_three he)
  obtain ⟨v,rfl⟩ := hu
  have hd0 : d ≠ 0 := by
    intro hd0
    rw [hd0, zero_dvd_iff] at hd
    norm_num at hd
  have hvi : norm (↑v⁻¹ : Eisenstein) = 1 := by
    rw [← normNat_cast, normNat_of_isUnit (Units.isUnit _), Nat.cast_one]
  refine ⟨d*(↑v⁻¹ : Eisenstein),e*(↑v : Eisenstein),mul_ne_zero hd0 (Units.ne_zero _),?_,hprim,?_,?_⟩
  · rw [norm_mul_eq, hvi, mul_one]
    have h := norm_le_of_dvd (by norm_num : (3 : Eisenstein) ≠ 0) hd
    have h3 : norm (3 : Eisenstein) = 9 := by
      change Complex.normSq (3 : ℂ) = 9
      norm_num
    simpa only [h3] using h
  · have hes : Squarefree e := (hde ▸ hs).of_mul_right
    exact squarefree_mul_iff.mpr ⟨((isCoprime_zero_left.mpr (Units.isUnit v)).of_isCoprime_of_dvd_left (dvd_zero e)).isRelPrime,hes,
      (Units.isUnit v).squarefree⟩
  · rw [hde]
    simp [mul_assoc, mul_left_comm, mul_comm]

end CubicFirstMoment

namespace CubicFirstMoment

theorem full_cube_decomposition {n : Eisenstein} (hn : n ≠ 0) :
    ∃ r s t c : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      c ≠ 0 ∧ n = r*s*t^2*c^3 := by
  obtain ⟨s₀,t₀,c,hs₀,ht₀,hst,hn'⟩ := cube_decomposition n
  obtain ⟨r,s,hr0,hr,hs,hss,hs'⟩ := squarefree_primary_residual s₀ hs₀
  obtain ⟨q,t,hq0,hq,ht,hst',ht'⟩ := squarefree_primary_residual t₀ ht₀
  have hc0 : c ≠ 0 := by intro hc; simp [hc] at hn'; exact hn hn'
  have hcop : IsCoprime s t :=
    hst.of_isCoprime_of_dvd_left (hs' ▸ dvd_mul_left s r) |>.of_isCoprime_of_dvd_right
      (ht' ▸ dvd_mul_left t q)
  refine ⟨r*q^2,s,t,c,mul_ne_zero hr0 (pow_ne_zero _ hq0),?_,hs,ht,hss,hst',hcop,hc0,?_⟩
  · rw [norm_mul_eq]
    have he : norm (q^2) = norm q ^ 2 := by simp [pow_two]
    rw [he]
    have hq2 : norm q ^ 2 ≤ 81 := by nlinarith [norm_nonneg q]
    nlinarith [norm_nonneg r, sq_nonneg (norm q)]
  · rw [hn',hs',ht']; ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric decay, cube frequency dyads and numerical block inequalities. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_squarefreePrimaryDyad {n : Eisenstein} {j : ℕ} :
    n ∈ squarefreePrimaryDyad j ↔ n ∈ frequencyDyad j ∧ primary n ∧ Squarefree n := by
  simp [squarefreePrimaryDyad]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GlobalRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem norm_gauss_le_one {a : Eisenstein} (ha : primary a) : ‖gauss a‖ ≤ 1 := by
  rw [norm_gauss ha]
  split_ifs <;> norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramOperator
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From Gram row sums to character-polynomial bounds

Finite duality turns the row-sum bound into an operator estimate. This is
the Cauchy/Gram step used after the multiplicity argument in the exceptional-character-moment argument.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

lemma complex_sum_norm_sq_expansion {ι : Type*} (P : Finset ι) (z : ι → ℂ) :
    ((‖∑ p ∈ P, z p‖^2 : ℝ) : ℂ) = ∑ p ∈ P, ∑ q ∈ P, z p * star (z q) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [starRingEnd_apply, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorDispersion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dispersion after a square-divisor restriction

The squarefree majorant introduces `d² ∣ a`. Expanding the actual
variance and changing variables produces a Gram kernel at scale
`A / N(d)²`, with the precise cubic-character factor retained.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorCharacterGram_scale {d p q : Eisenstein}
    (hd : primary d) (hp : primary p) (hq : primary q)
    (W : ℝ → ℂ) (A : ℝ) :
    divisorCharacterGram d p q W A =
      mixedSymbol p q (d^2)*primaryCharacterGram p q W (A/(norm d)^2) := by
  have hd2 : primary (d^2) := by simpa only [pow_two] using primary_mul hd hd
  have he := primaryCharacterGram_divisor_scale hp hq hd2 W A
  simpa only [divisorCharacterGram,pow_two,norm_mul_eq] using he

/-- The restricted variance is still the exact finite Gram quadratic form. -/
theorem divisorDispersionVariance_gram (d : Eisenstein) (B : Finset Eisenstein)
    (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    divisorDispersionVariance d B β u W A =
      ∑ p ∈ B, ∑ q ∈ B, dispersionAmplitude β u p*star (dispersionAmplitude β u q)*
        divisorCharacterGram d q p W A := by
  let H (p q a : Eisenstein) : ℂ := dispersionAmplitude β u p*star (dispersionAmplitude β u q)*
    (if primary a ∧ d^2 ∣ a then W (norm a/A)*cubicSymbol q a*star (cubicSymbol p a) else 0)
  have hsum (p : Eisenstein) (hp : p ∈ B) (q : Eisenstein) (hq : q ∈ B) :
      Summable (H p q) := by
    apply Summable.mul_left
    exact summable_gram_restricted (hB q hq) (hB p hp) W hW hW' hA (fun a => d^2 ∣ a)
  have hpoint (a : Eisenstein) :
      (if primary a ∧ d^2 ∣ a then W (norm a/A)*
        ((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0) =
      ∑ p ∈ B, ∑ q ∈ B, H p q a := by
    by_cases ha : primary a ∧ d^2 ∣ a
    · simp only [H,ite_eq_left ha,dispersionPolynomial]
      change W (norm a/A)*((‖∑ p ∈ B, dispersionAmplitude β u p*star (cubicSymbol p a)‖^2 : ℝ) : ℂ) = _
      rw [complex_sum_norm_sq_expansion,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [star_mul,star_star]
      ring
    · simp [ha,H]
  unfold divisorDispersionVariance
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun p hp => summable_sum (fun q hq => hsum p hp q hq))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Summable.tsum_finsetSum (hsum p hp)]
  apply Finset.sum_congr rfl
  intro q hq
  exact tsum_mul_left

/-- The `d²` restriction has norm cost `N(d)²` and the expected character
phase. No coprimality condition is dropped in this identity. -/
theorem divisorDispersionVariance_scaled {d : Eisenstein} (hd : primary d)
    (B : Finset Eisenstein) (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    divisorDispersionVariance d B β u W A =
      ∑ p ∈ B, ∑ q ∈ B, dispersionAmplitude β u p*star (dispersionAmplitude β u q)*
        mixedSymbol q p (d^2)*primaryCharacterGram q p W (A/(norm d)^2) := by
  rw [divisorDispersionVariance_gram d B hB β u W hW hW' hA]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [divisorCharacterGram_scale hd (hB q hq) (hB p hp) W A]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-length convolutions of arbitrary primary elements. The divisor
bound absorbs the tuple multiplicity in any positive norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedPrimarySupport_primary (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ a ∈ S i, primary a) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) : primary b := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  exact primary_finset_prod _ _ (fun i _ => hS i (f i) (Fintype.mem_piFinset.mp hf i))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic multiplicities and moments of products of finitely many prime powers. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

/-- A fixed logarithmic power is bounded by every positive norm power,
with an explicit constant uniform down to norm one. -/
lemma natLog_power_bound (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((Nat.log 2 n + 1 : ℕ) : ℝ)^m ≤ C*(n:ℝ)^ε := by
  by_cases hm : m = 0
  · subst m
    refine ⟨1,zero_lt_one,?_⟩
    intro n hn
    simpa using Real.one_le_rpow (by exact_mod_cast hn) hε.le
  let δ : ℝ := ε/m
  have hm0 : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hδ : 0 < δ := div_pos hε hm0
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := 1/(δ*Real.log 2)+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A^m,pow_pos hA _,?_⟩
  intro n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := zero_lt_one.trans_le hn1
  have hlog : (Nat.log 2 n:ℝ) ≤ Real.log n/Real.log 2 := by
    change (Nat.log 2 n:ℝ) ≤ Real.logb (2:ℝ) (n:ℝ)
    rw [← Real.natFloor_logb_natCast 2 n]
    exact Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hn1)
  have hx : 1 ≤ (n:ℝ)^δ := Real.one_le_rpow hn1 hδ.le
  have hbase : ((Nat.log 2 n+1:ℕ):ℝ) ≤ A*(n:ℝ)^δ := by
    push_cast
    calc
      _ ≤ Real.log n/Real.log 2+1 := by linarith
      _ ≤ ((n:ℝ)^δ/δ)/Real.log 2+(n:ℝ)^δ :=
        add_le_add (div_le_div_of_nonneg_right (Real.log_le_rpow_div hn0.le hδ) hL.le) hx
      _ = _ := by dsimp [A]; ring
  have he : ((n:ℝ)^δ)^m = (n:ℝ)^ε := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    dsimp [δ]
    exact div_mul_cancel₀ ε (ne_of_gt hm0)
  calc
    _ ≤ (A*(n:ℝ)^δ)^m := pow_le_pow_left₀ (by positivity) hbase m
    _ = _ := by rw [mul_pow,he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite realization of the literal prime convolution: each coordinate
contains every primary prime on which its independent weight is nonzero. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_mem_iff {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hhi : ∀ i x, R < x → W i x = 0) (i : ι) (p : Eisenstein) :
    p ∈ fullPrimeSupport R W X i ↔ primaryPrime p ∧ W i (norm p/X i) ≠ 0 := by
  simp only [fullPrimeSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨⟨hp,_⟩,hw⟩,hq⟩
    exact ⟨⟨hp,hq⟩,hw⟩
  · rintro ⟨⟨hp,hq⟩,hw⟩
    have hn : norm p/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
    exact ⟨⟨⟨hp,(div_le_iff₀ (hX i)).mp hn⟩,hw⟩,hq⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullStructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary published mean-value theorem applied to the literal
prime convolution, with every numerator and excluded-prime factor retained. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_prime (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    ∀ i, ∀ z ∈ fullPrimeSupport R W X i, primaryPrime z := by
  intro i z hz
  exact ⟨(mem_primaryElementBall.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1,
    (Finset.mem_filter.mp hz).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite low-conductor frequency support: a small
nonzero core times a bounded cube, with precisely the cubes removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_lowNoncubeSupport {V J : ℝ} {h : Eisenstein} (hh : h ∈ lowNoncubeSupport V J) :
    (¬∃ a : Eisenstein, a^3 = h) ∧ ∃ v j : Eisenstein,
      v ≠ 0 ∧ j ≠ 0 ∧ norm v ≤ V ∧ norm j ≤ J ∧ h = v*j^3 := by
  obtain ⟨hi,hn⟩ := Finset.mem_filter.mp hh
  obtain ⟨⟨v,j⟩,hm,he⟩ := Finset.mem_image.mp hi
  have hv := mem_nonzeroNormBall.mp (Finset.mem_product.mp hm).1
  have hj := mem_nonzeroNormBall.mp (Finset.mem_product.mp hm).2
  exact ⟨hn,v,j,hv.2,hj.2,hv.1,hj.1,he.symm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicCoreCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coverage of a noncube frequency by either the low-core set or
a ramified/squarefree pair of large conductor. No decomposition is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_cube (j : Eisenstein) : norm (j^3) = norm j^3 := by
  simp only [pow_succ,norm_mul_eq,pow_zero,norm_one_eq]

lemma cube_part_norm_bound {h v j : Eisenstein} {H : ℝ}
    (hv : v ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H) :
    norm j ≤ H^(1/3:ℝ) := by
  have hcube : norm j^3 ≤ H := by
    calc
      _ ≤ norm v*norm j^3 := le_mul_of_one_le_left (pow_nonneg (norm_nonneg j) _) (one_le_norm hv)
      _ = norm h := by rw [heq,norm_mul_eq,norm_cube]
      _ ≤ H := hh
  have hp := Real.rpow_le_rpow (pow_nonneg (norm_nonneg j) 3) hcube (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (norm j^3)^(1/3:ℝ) = norm j := by
    rw [← Real.rpow_natCast (norm j) 3,← Real.rpow_mul (norm_nonneg j)]
    norm_num
  rwa [he] at hp

lemma mem_lowNoncubeSupport_of_core {h v j : Eisenstein} {V H : ℝ}
    (hv : v ≠ 0) (hj : j ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H)
    (hsmall : norm v ≤ V) (hn : ¬∃ a : Eisenstein, a^3 = h) :
    h ∈ lowNoncubeSupport V (H^(1/3:ℝ)) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(v,j),?_,heq.symm⟩,hn⟩
  exact Finset.mem_product.mpr ⟨mem_nonzeroNormBall.mpr ⟨hsmall,hv⟩,
    mem_nonzeroNormBall.mpr ⟨cube_part_norm_bound hv heq hh,hj⟩⟩

theorem noncube_large_core_decomposition {h : Eisenstein} {V H : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ H) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (H^(1/3:ℝ))) :
    ∃ r s t j : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      j ≠ 0 ∧ h = r*s*t^2*j^3 ∧
      V/729 < norm s*norm t^2 ∧ norm s*norm t^2 ≤ H ∧ norm j ≤ H^(1/3:ℝ) := by
  obtain ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq⟩ := full_cube_decomposition hh0
  have hv : r*s*t^2 ≠ 0 := mul_ne_zero (mul_ne_zero hr (primary_ne_zero hs))
    (pow_ne_zero _ (primary_ne_zero ht))
  have hcore : h = (r*s*t^2)*j^3 := heq
  have hlarge : V < norm (r*s*t^2) := lt_of_not_ge (fun hsmall => hnot
    (mem_lowNoncubeSupport_of_core hv hj hcore hh hsmall hn))
  have hc : norm (r*s*t^2) = norm r*(norm s*norm t^2) := by
    rw [norm_mul_eq,norm_mul_eq]
    have ht2 : norm (t^2) = norm t^2 := by simp only [pow_two,norm_mul_eq]
    rw [ht2]
    ring
  have hD0 : 0 ≤ norm s*norm t^2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hsmall : norm (r*s*t^2) ≤ norm h := by
    calc
      _ ≤ norm (r*s*t^2)*norm (j^3) :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_norm (pow_ne_zero _ hj))
      _ = norm h := by simp only [hcore,norm_mul_eq]
  refine ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq,?_,?_,cube_part_norm_bound hv hcore hh⟩
  · apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 729)).mpr
    rw [hc] at hlarge
    nlinarith [mul_le_mul_of_nonneg_right hrN hD0]
  · apply le_trans _ (hsmall.trans hh)
    rw [hc]
    exact le_mul_of_one_le_left hD0 (one_le_norm hr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cover of all noncube frequencies outside the small-core set
by the actual coprime ramified/squarefree blocks used in the moment bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coreDyadicConductor_pos (i j : ℕ) : 0 < coreDyadicConductor i j := by
  unfold coreDyadicConductor
  positivity

lemma squarefreePrimaryDyad_gramDyad {i : ℕ} {s : Eisenstein}
    (hs : s ∈ squarefreePrimaryDyad i) : gramDyad ((2:ℝ)^i) s := by
  obtain ⟨hf,hp,hq⟩ := mem_squarefreePrimaryDyad.mp hs
  have hlog := (mem_frequencyDyad.mp hf).2
  refine ⟨hp,hq,(frequencyDyad_norm hf).1,?_⟩
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (normNat s)
  rw [hlog] at hlt
  have hcast : norm s < (2:ℝ)^(i+1) := by
    rw [← normNat_cast]
    exact_mod_cast hlt
  simpa only [pow_succ,mul_comm] using hcast

lemma real_cube_scale_bound {x B D : ℝ} (hx : 0 ≤ x) (hD : 0 < D)
    (h : x^3*D ≤ B) : x ≤ (B/D)^(1/3:ℝ) := by
  have hc : x^3 ≤ B/D := (le_div_iff₀ hD).mpr h
  have hp := Real.rpow_le_rpow (pow_nonneg hx 3) hc (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (x^3)^(1/3:ℝ) = x := by
    rw [← Real.rpow_natCast x 3,← Real.rpow_mul hx]
    norm_num
  rwa [he] at hp

theorem noncube_mem_coreDyadicBlock {h : Eisenstein} {V B : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ B) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) :
    ∃ z ∈ largeCoreDyadicIndices V B, h ∈ coreDyadicBlock B z.1 z.2 := by
  obtain ⟨r,s,t,c,hr,hrN,hs,ht,hss,hst,hcop,hc,heq,hlarge,hcore,hcN⟩ :=
    noncube_large_core_decomposition hh0 hh hn hnot
  let i := Nat.log 2 (normNat s)
  let j := Nat.log 2 (normNat t)
  have hsD : s ∈ squarefreePrimaryDyad i := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero hs,rfl⟩,hs,hss⟩
  have htD : t ∈ squarefreePrimaryDyad j := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero ht,rfl⟩,ht,hst⟩
  have hsG := squarefreePrimaryDyad_gramDyad hsD
  have htG := squarefreePrimaryDyad_gramDyad htD
  have hDlo : coreDyadicConductor i j ≤ norm s*norm t^2 := by
    exact mul_le_mul hsG.2.2.1 (pow_le_pow_left₀ (by positivity) htG.2.2.1 2)
      (by positivity) (norm_nonneg s)
  have hDhi : norm s*norm t^2 < 8*coreDyadicConductor i j := by
    have ht2 : norm t^2 < (2*(2:ℝ)^j)^2 :=
      (pow_lt_pow_left₀ htG.2.2.2 (norm_nonneg t) (by norm_num : (2:ℕ) ≠ 0))
    calc
      _ < (2*(2:ℝ)^i)*((2*(2:ℝ)^j)^2) := mul_lt_mul hsG.2.2.2 ht2.le
        (sq_pos_of_pos (zero_lt_one.trans_le (one_le_norm (primary_ne_zero ht)))) (by positivity)
      _ = _ := by unfold coreDyadicConductor; ring
  have hDb : coreDyadicConductor i j ≤ B := hDlo.trans hcore
  have hidx : ∀ (a : Eisenstein), primary a → norm a ≤ B →
      Nat.log 2 (normNat a) < Nat.log 2 ⌊B⌋₊+1 := by
    intro a ha haB
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    apply Nat.le_floor
    rwa [normNat_cast]
  have hsB : norm s ≤ B := (le_mul_of_one_le_right (norm_nonneg s)
    (one_le_pow₀ (one_le_norm (primary_ne_zero ht)))).trans hcore
  have htB : norm t ≤ B := by
    have htt : norm t ≤ norm t^2 := by
      nlinarith [one_le_norm (primary_ne_zero ht)]
    exact htt.trans ((le_mul_of_one_le_left (sq_nonneg _) (one_le_norm (primary_ne_zero hs))).trans hcore)
  have hcube : norm c^3*coreDyadicConductor i j ≤ B := by
    have hn : norm h = norm r*(norm s*norm t^2)*norm c^3 := by
      simp only [heq,norm_mul_eq,norm_cube,pow_two]
      ring
    calc
      _ ≤ norm c^3*(norm s*norm t^2) := mul_le_mul_of_nonneg_left hDlo (pow_nonneg (norm_nonneg c) _)
      _ ≤ norm r*(norm s*norm t^2)*norm c^3 := by
        nlinarith [mul_le_mul_of_nonneg_right
          (one_le_norm hr) (mul_nonneg (mul_nonneg (norm_nonneg s) (sq_nonneg (norm t)))
            (pow_nonneg (norm_nonneg c) 3))]
      _ = norm h := hn.symm
      _ ≤ B := hh
  refine ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (hidx s hs hsB),Finset.mem_range.mpr (hidx t ht htB)⟩,
    ⟨by dsimp only; linarith,hDb⟩⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨((r,c),(s,t)),Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨mem_nonzeroNormBall.mpr ⟨hrN,hr⟩,mem_nonzeroNormBall.mpr
      ⟨real_cube_scale_bound (norm_nonneg c) (coreDyadicConductor_pos i j) hcube,hc⟩⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsD,htD⟩,hcop⟩⟩,heq.symm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicFrequencyMassSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete small-core / dyadic-core partition of a finite noncube
mass. Multiple arithmetic decompositions cost no frequency multiplicity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem noncube_frequency_mass_split (H : Finset Eisenstein) {V B : ℝ}
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h)
    (f : Eisenstein → ℝ) (hf : ∀ h, 0 ≤ f h) :
    (∑ h ∈ H, f h) ≤
      (∑ h ∈ H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))), f h)+
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
  let I := (largeCoreDyadicIndices V B).sigma (fun z => coreDyadicBlock B z.1 z.2)
  let F : Sigma (fun _ : ℕ × ℕ => Eisenstein) → Eisenstein := Sigma.snd
  have hcover : H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) ⊆ I.image F := by
    intro h hh
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hh
    obtain ⟨z,hz,hb⟩ := noncube_mem_coreDyadicBlock (hH h hm).1
      (hH h hm).2.1 (hH h hm).2.2 hn
    exact Finset.mem_image.mpr ⟨⟨z,h⟩,Finset.mem_sigma.mpr ⟨hz,hb⟩,rfl⟩
  have hsum : (∑ h ∈ H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))), f h) ≤
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hf h)).trans
    apply (Finset.sum_image_le_of_nonneg (s := I) (g := F) (f := f) (fun h _ => hf h)).trans_eq
    exact Finset.sum_sigma _ _ _
  rw [← Finset.sum_filter_add_sum_filter_not H
    (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))) f]
  exact add_le_add le_rfl hsum

lemma largeCoreDyadicIndices_card (V B : ℝ) :
    (largeCoreDyadicIndices V B).card ≤ (Nat.log 2 ⌊B⌋₊+1)^2 := by
  unfold largeCoreDyadicIndices
  apply (Finset.card_filter_le _ _).trans
  exact le_of_eq ((Finset.card_product _ _).trans (by simp only [Finset.card_range,pow_two]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeOuterSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full outer cubic-sieve estimate for finite noncube frequencies,
derived by covering with the actual core dyads and summing their bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma lowNoncubeSupport_zero (J : ℝ) : lowNoncubeSupport 0 J = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro h hh
  obtain ⟨_,v,j,hv,_,hNv,_,_⟩ := mem_lowNoncubeSupport hh
  have hv1 := one_le_norm hv
  linarith

theorem noncube_outer_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ),
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  have he : 0 < ε/2 := by linarith
  obtain ⟨C,hC,hblock⟩ := outer_core_block_sieve he
  obtain ⟨D,hD,hlog⟩ := natLog_power_bound 2 he
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro S H B N hB hN hS hH β
  have hB0 := zero_le_one.trans hB
  have hN0 := zero_le_one.trans hN
  have hcount : ((largeCoreDyadicIndices 0 B).card:ℝ) ≤ D*B^(ε/2) := by
    calc
      _ ≤ ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ)^2 := by
        exact_mod_cast largeCoreDyadicIndices_card 0 B
      _ ≤ D*(⌊B⌋₊:ℝ)^(ε/2) := hlog _ ((Nat.one_le_floor_iff B).mpr hB)
      _ ≤ D*B^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hB0) he.le) hD.le
  have hsplit := noncube_frequency_mass_split (V := 0) H hH
    (fun h => ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) (fun _ => sq_nonneg _)
  simp only [lowNoncubeSupport_zero,Finset.notMem_empty,Finset.filter_false,
    Finset.sum_empty,zero_add] at hsplit
  have hrows (z : ℕ × ℕ) (hz : z ∈ largeCoreDyadicIndices 0 B) :=
    hblock S (coreDyadicBlock B z.1 z.2) B N z.1 z.2 hB0 hN
      (Finset.mem_filter.mp hz).2.2 hS (fun _ h => h) β
  have hE : 0 ≤ ∑ n ∈ S, ‖β n‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : B^(ε/2)*(2*B*N)^(ε/2) ≤ (2*B*N)^ε := by
    calc
      _ ≤ (2*B*N)^(ε/2)*(2*B*N)^(ε/2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        apply Real.rpow_le_rpow hB0 _ he.le
        nlinarith
      _ = _ := by rw [← Real.rpow_add (by positivity : 0 < 2*B*N)]; congr 1; ring
  calc
    _ ≤ ∑ z ∈ largeCoreDyadicIndices 0 B,
        C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 :=
      hsplit.trans (Finset.sum_le_sum hrows)
    _ = ((largeCoreDyadicIndices 0 B).card:ℝ)*
        (C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2) := by simp
    _ ≤ (D*B^(ε/2))*
        (C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C*D)*(B^(ε/2)*(2*B*N)^(ε/2))*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*∑ n ∈ S, ‖β n‖^2 := by ring
    _ ≤ _ := by gcongr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AllFrequencyOuterSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Add the explicit cube frequencies to the proved outer sieve. The
cube count is a lattice count, not an additional analytic hypothesis. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_frequency_card_le (H : Finset Eisenstein) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ∃ j : Eisenstein, j^3 = h) :
    (H.card:ℝ) ≤ 18*B^(1/3:ℝ) := by
  have hs : H ⊆ (nonzeroNormBall (B^(1/3:ℝ))).image (fun j => j^3) := by
    intro h hh
    obtain ⟨hne,hn,j,rfl⟩ := hH h hh
    have hj : j ≠ 0 := fun hj => hne (by rw [hj,zero_pow (by decide)])
    have hpow : (norm j)^3 ≤ B := by simpa only [eisenstein_norm_pow] using hn
    have hr := Real.rpow_le_rpow (pow_nonneg (norm_nonneg j) 3) hpow
      (by norm_num : (0:ℝ) ≤ 1/3)
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg j)] at hr
    norm_num at hr
    exact Finset.mem_image.mpr ⟨j,mem_nonzeroNormBall.mpr ⟨hr,hj⟩,rfl⟩
  exact (Nat.cast_le.mpr ((Finset.card_le_card hs).trans Finset.card_image_le)).trans
    (nonzeroNormBall_card_le (Real.rpow_nonneg hB _))

lemma cubic_character_row_sq (S : Finset Eisenstein)
    (hS : ∀ n ∈ S, primary n) (β : Eisenstein → ℂ) (h : Eisenstein) :
    ‖∑ n ∈ S, β n*cubicSymbol n h‖^2 ≤ (S.card:ℝ)*∑ n ∈ S, ‖β n‖^2 := by
  have hn : ‖∑ n ∈ S, β n*cubicSymbol n h‖ ≤ ∑ n ∈ S, ‖β n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS n hn) _)
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) hn 2).trans
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
    Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun n => ‖β n‖)

theorem all_frequency_outer_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ),
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) → ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := noncube_outer_sieve hε
  refine ⟨C+324,by positivity,?_⟩
  intro S H B N hB hN hS hH β
  let Q := H.filter (fun h => ∃ j : Eisenstein, j^3 = h)
  let T := H.filter (fun h => ¬∃ j : Eisenstein, j^3 = h)
  let E := ∑ n ∈ S, ‖β n‖^2
  let P := B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hscale : 1 ≤ (2*B*N)^ε := Real.one_le_rpow (by nlinarith) hε.le
  have hnc := hbound S T B N hB hN hS (fun h hh =>
    ⟨(hH h (Finset.mem_filter.mp hh).1).1,
      (hH h (Finset.mem_filter.mp hh).1).2,(Finset.mem_filter.mp hh).2⟩) β
  have hcube : (∑ h ∈ Q, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤ 324*P*E := by
    have hc := cube_frequency_card_le Q (zero_le_one.trans hB) (fun h hh =>
      ⟨(hH h (Finset.mem_filter.mp hh).1).1,
        (hH h (Finset.mem_filter.mp hh).1).2,(Finset.mem_filter.mp hh).2⟩)
    have hs := primary_support_card_le S (zero_le_one.trans hN)
      (fun n hn => ⟨(hS n hn).1,(hS n hn).2.2⟩)
    calc
      _ ≤ ∑ _h ∈ Q, (S.card:ℝ)*E := Finset.sum_le_sum (fun _ _ =>
        cubic_character_row_sq S (fun n hn => (hS n hn).1) β _)
      _ = (Q.card:ℝ)*((S.card:ℝ)*E) := by simp
      _ ≤ (18*B^(1/3:ℝ))*((18*N)*E) := by gcongr
      _ ≤ 324*P*E := by
        dsimp only [P]
        have hp : B^(1/3:ℝ)*N ≤ B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N := by
          exact le_add_of_nonneg_left (add_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg (by positivity) _))
        nlinarith [mul_le_mul_of_nonneg_right hp hE]
  have heq : (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) =
      (∑ h ∈ Q, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) +
      ∑ h ∈ T, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2 := by
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [heq]
  apply (add_le_add hcube hnc).trans
  change 324*P*E+C*(2*B*N)^ε*P*E ≤ (C+324)*(2*B*N)^ε*P*E
  have hh := mul_le_mul_of_nonneg_right hscale (mul_nonneg hP hE)
  nlinarith

lemma all_frequency_cubic_operator_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ),
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      finiteCubicBound S H ≤ C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N) := by
  obtain ⟨C,hC,hbound⟩ := all_frequency_outer_sieve hε
  refine ⟨C,hC,?_⟩
  intro S H B N hB hN hS hH
  exact (finiteCubicBound_le_iff S H (by positivity)).mpr (hbound S H B N hB hN hS hH)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramStructuredRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rows in the Poisson kernel are exactly the full structured prime
sums, including the squarefree restriction and the reversal of Mellin height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullSquarefreePrimeSupport_primary (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) {b : Eisenstein} (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
    primary b ∧ Squarefree b := by
  have hm := Finset.mem_filter.mp hb
  exact ⟨orderedPrimarySupport_primary _ (fun i b hb => (fullPrimeSupport_prime R W X i b hb).1) hm.1,hm.2.1⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
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

lemma wideGramMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (wideGramMellinCoefficient M hM W hW hW' ρ) :=
  (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ)).integrable

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

theorem wide_radial_mellin_separated (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ}
    (hρ : 0 ≤ ρ) (hx : 0 < x) (hy : 0 < y) (hxy : |Real.log x-Real.log y| ≤ M) :
    radialDualProfile W (ρ*x/y) = ∫ t : ℝ,
      wideGramMellinCoefficient M hM W hW hW' ρ t*gramMellinPhase t x*star (gramMellinPhase t y) := by
  have hk := wideGramLogKernel_eq_radial M hM W hρ hxy
  rw [Real.exp_sub,Real.exp_log hx,Real.exp_log hy,← mul_div_assoc] at hk
  rw [← hk]
  have he := congrArg (fun f : 𝓢(ℝ,ℂ) => f (Real.log x-Real.log y))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ,ℂ))
      (wideGramLogSchwartz M hM W hW hW' ρ))
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at he
  change wideGramLogSchwartz M hM W hW hW' ρ (Real.log x-Real.log y) = _
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
    wideGramMellinCoefficient M hM W hW hW' ρ t = _
  rw [hp]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideCoprimeMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin separation of the actual coprime radial form on a fixed compact
norm range. The arithmetic rows are unchanged. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma wideGramMellinCoefficient_integrable_phases (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ x y : ℝ) :
    Integrable (fun t => wideGramMellinCoefficient M hM W hW hW' ρ t * gramMellinPhase t x *
      star (gramMellinPhase t y)) := by
  apply Integrable.mul_bdd (c := 1)
  · exact (wideGramMellinCoefficient_integrable M hM W hW hW' ρ).mul_bdd
      (gramMellinPhase_continuous x).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_gramMellinPhase t x).le))
  · exact (gramMellinPhase_continuous y).star.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp)


theorem wideCoprimeRadialForm_mellin (M : ℝ) (hM : 0 < M) (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, 0 < x h)
    (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    coprimeRadialForm S H v w phase x y W ρ = ∫ t : ℝ,
      wideGramMellinCoefficient M hM W hW hW' ρ t * coprimeMellinKernel S H v w phase x y t := by
  let F (h a b : Eisenstein) (t : ℝ) : ℂ :=
    (phase h * (if IsCoprime a b then
      (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0)) *
      (wideGramMellinCoefficient M hM W hW hW' ρ t * gramMellinPhase t (x h) *
        star (gramMellinPhase t (y a*y b)))
  have hF (h a b : Eisenstein) : Integrable (F h a b) :=
    (wideGramMellinCoefficient_integrable_phases M hM W hW hW' ρ (x h) (y a*y b)).const_mul _
  have he (h : Eisenstein) (hh : h ∈ H) (a : Eisenstein) (ha : a ∈ S)
      (b : Eisenstein) (hb : b ∈ S) :
      phase h * (if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) *
          radialDualProfile W (ρ*x h/(y a*y b)) else 0) = ∫ t, F h a b t := by
    rw [show (∫ t, F h a b t) = _ from integral_const_mul _ _]
    rw [← wide_radial_mellin_separated M hM W hW hW' hρ (hx h hh)
      (mul_pos (hy a ha) (hy b hb)) (hlog h hh a ha b hb)]
    split_ifs <;> ring
  calc
    _ = ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, ∫ t, F h a b t := by
      unfold coprimeRadialForm
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeNormRange
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma fullPrimeProduct_norm_bounds (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport (fullPrimeSupport R W X)) :
    (∏ i, X i) ≤ norm b ∧ norm b ≤ R^(Fintype.card ι)*(∏ i, X i) := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  have hbound (i : ι) : X i ≤ norm (f i) ∧ norm (f i) ≤ R*X i := by
    have hmem := Fintype.mem_piFinset.mp hf i
    have hw := ((fullPrimeSupport_mem_iff W X hX hhi i (f i)).mp hmem).2
    constructor
    · have hn : 1 ≤ norm (f i)/X i := le_of_not_gt (fun h => hw (hlo i _ h))
      simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hn
    · have hn : norm (f i)/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
      exact (div_le_iff₀ (hX i)).mp hn
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod (fun i _ => (hX i).le) (fun i _ => (hbound i).1)
  · calc
      _ ≤ ∏ i, R*X i := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hbound i).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem schwartz_wideGramExp_comp_uniform (M : ℝ) (hM : 0 ≤ M) (F : 𝓢(ℂ, ℂ)) (n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c → ∀ u : ℝ, |u| ≤ 2*M →
      (1+c)^K * ‖iteratedFDeriv ℝ n (fun v => F (c • gramExp v)) u‖ ≤ C := by
  obtain ⟨D, hD, hderiv⟩ := wideGramExp_deriv_bound M n
  let L := n+K
  let S := (Finset.Iic (L,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  let H := (Real.exp M)^L * 2^L * S
  have hS : 0 ≤ S := by positivity
  have hH : 0 ≤ H := by positivity
  refine ⟨(n.factorial : ℝ)*H*D^n, by positivity, ?_⟩
  intro c hc u hu
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


lemma wideAnnularLogSchwartz_deriv_zero (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (c u : ℝ) (n : ℕ)
    (hu : ¬ |u| ≤ 2*M) : iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u = 0 := by
  by_contra hn
  have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := wideAnnularLogSchwartz M hM F c) n hn
  have hb := tsupport_smul_subset_left ((wideGramLogBump M hM) : ℝ → ℝ)
    (fun v => F (c • gramExp v)) hs
  rw [(wideGramLogBump M hM).tsupport_eq] at hb
  exact hu (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, wideGramLogBump] using hb)

theorem wideAnnularLogSchwartz_seminorm_uniform (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (wideAnnularLogSchwartz M hM F c) ≤ C := by
  choose C hC hbound using fun i => schwartz_wideGramExp_comp_uniform M hM.le F i K
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) * C (n-i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hC (n-i)))
  refine ⟨(2*M)^k * B, by positivity, ?_⟩
  intro c hc
  have hp : 0 < (1+c)^K := pow_pos (by positivity) _
  rw [← le_div_iff₀' hp]
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ 2*M
  · rw [le_div_iff₀' hp]
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (wideGramLogBump M hM).contDiff
      ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)) u (n := n) (mod_cast le_top)
    have hd' : (1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖ ≤ B := by
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
        _ ≤ B := by
          apply Finset.sum_le_sum
          intro i hi
          have hb : ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ ≤
              SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) := by
            have hb := SchwartzMap.le_seminorm ℝ 0 i (wideGramBumpSchwartz M hM) u
            rw [show (wideGramBumpSchwartz M hM : ℝ → ℝ) = ((wideGramLogBump M hM) : ℝ → ℝ) from rfl] at hb
            simpa only [pow_zero, one_mul] using hb
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity))
            (hbound (n-i) c hc u hu) (by positivity) (by positivity)
    calc
      _ = ‖u‖^k * ((1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖) := by ring
      _ ≤ (2*M)^k * B := mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hu) k) hd' (by positivity) (by positivity)
  · rw [wideAnnularLogSchwartz_deriv_zero M hM F c u n hu, norm_zero, mul_zero]
    positivity

theorem wideAnnularLogSchwartz_fourier_uniform (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (𝓕 (wideAnnularLogSchwartz M hM F c)) ≤ C := by
  let f : ℝ → 𝓢(ℝ, ℂ) := fun c => (1+c)^K • wideAnnularLogSchwartz M hM F c
  have hb : Bornology.IsVonNBounded ℝ (f '' Set.Ici 0) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C, hC, hc⟩ := wideAnnularLogSchwartz_seminorm_uniform M hM F i.1 i.2 K
    refine ⟨C+1, by linarith, ?_⟩
    intro c hc0
    have hc0' : 0 ≤ c := hc0
    change SchwartzMap.seminorm ℝ i.1 i.2 ((1+c)^K • wideAnnularLogSchwartz M hM F c) < _
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (pow_pos (by linarith) _)]
    exact (hc c hc0).trans_lt (by linarith)
  have hbf := hb.image (SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ))
  obtain ⟨C, hC, hc⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hbf (k,n)
  refine ⟨C, hC, ?_⟩
  intro c hc0
  have hmem : SchwartzMap.fourierTransformCLM ℝ (f c) ∈
      SchwartzMap.fourierTransformCLM ℝ '' (f '' Set.Ici 0) :=
    ⟨f c, ⟨c, hc0, rfl⟩, rfl⟩
  have h := hc _ hmem
  change SchwartzMap.seminorm ℝ k n
    (SchwartzMap.fourierTransformCLM ℝ ((1+c)^K • wideAnnularLogSchwartz M hM F c)) < C at h
  rw [map_smul, map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos (pow_pos (by linarith) _)] at h
  exact h.le

theorem wideAnnularLogSchwartz_fourier_L1_uniform (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * (∫ t : ℝ, ‖𝓕 (wideAnnularLogSchwartz M hM F c) t‖) ≤ C := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k * ∫ t : ℝ, (1+‖t‖)^(-(k : ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun t => by positivity))
  obtain ⟨C₀, hC₀, hc₀⟩ := wideAnnularLogSchwartz_fourier_uniform M hM F 0 0 K
  obtain ⟨C₁, hC₁, hc₁⟩ := wideAnnularLogSchwartz_fourier_uniform M hM F k 0 K
  refine ⟨D*(C₀+C₁)+1, by positivity, ?_⟩
  intro c hc
  have h := (𝓕 (wideAnnularLogSchwartz M hM F c)).integral_pow_mul_iteratedFDeriv_le ℝ volume 0 0
  simp only [pow_zero, norm_iteratedFDeriv_zero, one_mul, zero_add] at h
  have hb : (1+c)^K * (∫ t : ℝ, ‖𝓕 (wideAnnularLogSchwartz M hM F c) t‖) ≤ D*(C₀+C₁) := by
    calc
      _ ≤ (1+c)^K * (D * (SchwartzMap.seminorm ℝ 0 0 (𝓕 (wideAnnularLogSchwartz M hM F c)) +
            SchwartzMap.seminorm ℝ k 0 (𝓕 (wideAnnularLogSchwartz M hM F c)))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = D*((1+c)^K * SchwartzMap.seminorm ℝ 0 0 (𝓕 (wideAnnularLogSchwartz M hM F c)) +
            (1+c)^K * SchwartzMap.seminorm ℝ k 0 (𝓕 (wideAnnularLogSchwartz M hM F c))) := by ring
      _ ≤ D*(C₀+C₁) := mul_le_mul_of_nonneg_left (add_le_add (hc₀ c hc) (hc₁ c hc)) hD
  linarith

lemma wideAnnularLogSchwartz_eq_wideGramLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ) =
      wideGramLogSchwartz M hM W hW hW' ρ := by
  ext u
  simp only [wideAnnularLogSchwartz_apply M hM, wideGramLogSchwartz_apply, wideGramLogKernel,
    normProfileFourierSchwartz_apply]
  congr 2
  simp only [gramExp, Complex.real_smul, Complex.ofReal_mul]

theorem wideGramMellinCoefficient_mass_rapidDecay (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * (∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖) ≤ C := by
  obtain ⟨C, hC, hc⟩ := wideAnnularLogSchwartz_fourier_L1_uniform M hM
    (normProfileFourierSchwartz W hW hW') (2*A)
  refine ⟨C, hC, ?_⟩
  intro ρ hρ
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ, Real.sqrt_nonneg ρ]
  have h := hc (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [wideAnnularLogSchwartz_eq_wideGramLogSchwartz M hM W hW hW' ρ] at h
  exact (mul_le_mul_of_nonneg_right hs (integral_nonneg (fun t => _root_.norm_nonneg _))).trans h

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeRoughDivisor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nontrivial common prime divisor of a rough prime convolution is
itself large. In the retained small-divisor range only the empty subset
survives; its coefficient remains the original convolution. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrime_prime_divisor_coordinate (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {b p : Eisenstein} (hp : primaryPrime p) (hpd : p ∣ b)
    (hb : b ∈ orderedConvolutionSupport (fullPrimeSupport R W X)) :
    ∃ i, p ∈ fullPrimeSupport R W X i := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨i,_,hi⟩ := (hp.2.dvd_finsetProd_iff f).mp hpd
  have hfi := Fintype.mem_piFinset.mp hf i
  have hfp := fullPrimeSupport_prime R W X i (f i) hfi
  have he : p = f i := primary_associated_eq hp.1 hfp.1
    ((hp.2.dvd_prime_iff_associated hfp.2).mp hi)
  exact ⟨i,he.symm ▸ hfi⟩

lemma fullPrime_nonempty_divisor_large {R D : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) (hrough : ∀ i, D < X i)
    (s : Finset Eisenstein) (hs : ∀ p ∈ s, primaryPrime p) (hsne : s.Nonempty)
    {b : Eisenstein} (hb : b ∈ orderedConvolutionSupport (fullPrimeSupport R W X))
    (hsd : (∏ p ∈ s, p) ∣ b) : D < norm (∏ p ∈ s, p) := by
  obtain ⟨p,hps⟩ := hsne
  have hp := hs p hps
  have hpf : p ∣ ∏ p ∈ s, p := Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hps
  obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R W X hp (hpf.trans hsd) hb
  have hw := ((fullPrimeSupport_mem_iff W X hX hhi i p).mp hi).2
  have hn : X i ≤ norm p := by
    have hratio : 1 ≤ norm p/X i := le_of_not_gt (fun h => hw (hlo i _ h))
    simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hratio
  have hf : (∏ p ∈ s, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hs p hp).2.ne_zero)
  exact (hrough i).trans_le (hn.trans (norm_le_of_dvd hf hpf))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonVarianceDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-divisor variance as actual character mass, followed by
its canonical common-factor decomposition. This is the bridge to the
wide dual recurrence on shortened rows. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorGramCoefficient_norm_le (d : Eisenstein) (β : Eisenstein → ℂ) (u : ℝ)
    {a : Eisenstein} (ha : primary a) : ‖divisorGramCoefficient d β u a‖ ≤ ‖β a‖ := by
  simp only [divisorGramCoefficient,norm_star,dispersionAmplitude,norm_mul,
    norm_normTwist,mul_one,divisorTwistedCoefficient,norm_star]
  have hg := norm_gauss_le_one ha
  have hc := norm_cubicSymbol_le_one ha (d^2)
  calc
    _ ≤ ‖β a‖*1*1 := by gcongr
    _ = _ := by ring

lemma divisorDispersionVariance_eq_primaryMass {d : Eisenstein} (hd : primary d)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    divisorDispersionVariance d S β u W A =
      primarySmoothedSieveMass S (divisorGramCoefficient d β u) W (A/(norm d)^2) := by
  have hdN := norm_pos_of_ne_zero (primary_ne_zero hd)
  rw [divisorDispersionVariance_scaled hd S hS β u W hW hW' hA,
    primarySmoothedSieveMass_gram S hS _ W hW hW' (by positivity)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [divisorGramCoefficient,dispersionAmplitude,divisorTwistedCoefficient,
    mixedSymbol,star_mul,star_star]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonGramRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

 theorem primaryMass_sub_coprime_common (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    primarySmoothedSieveMass S u W Z-coprimeGramForm S u W Z =
      ∑ k ∈ (commonRowFactors S).filter (· ≠ 1), commonGramBlock S u W Z k := by
  let F (a b : Eisenstein) : ℂ := if IsCoprime a b then 0 else
    u a*star (u b)*primaryCharacterGram a b W Z
  have hdiff : primarySmoothedSieveMass S u W Z-coprimeGramForm S u W Z =
      ∑ a ∈ S, ∑ b ∈ S, F a b := by
    rw [primarySmoothedSieveMass_gram S (fun a ha => (hS a ha).1) u W hW hW' hZ]
    unfold coprimeGramForm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : IsCoprime a b <;> simp [F,hab]
  rw [hdiff,common_factor_matrix_decomposition S hS F,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hkS
  have hk := commonRowFactors_spec hS hkS
  by_cases hk1 : k = 1
  · subst k
    simp only [ne_eq,not_true_eq_false,ite_false, if_false,F,one_mul]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hab : IsCoprime a b <;> simp [hab]
  · rw [ite_eq_left hk1]
    unfold commonGramBlock
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : IsCoprime a b
    · have hnot : ¬IsCoprime (k*a) (k*b) := by
        intro hc
        exact hk1 (primary_unit_eq_one
          (hc.isUnit_of_dvd' (dvd_mul_right k a) (dvd_mul_right k b)) hk.1)
      simp only [ite_eq_left hab,F,ite_eq_right hnot]
    · simp only [ite_eq_right hab]

lemma divisorCoprimeDispersionGram_eq_coprimeGram (d : Eisenstein) (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    divisorCoprimeDispersionGram d S β u W A =
      coprimeGramForm S (divisorGramCoefficient d β u) W (A/(norm d)^2) := by
  unfold divisorCoprimeDispersionGram coprimeDispersionGram coprimeGramForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,ite_eq_left hab.symm,divisorGramCoefficient,
      dispersionAmplitude,divisorTwistedCoefficient,star_mul,star_star]
    ring
  · simp only [ite_eq_right hab,ite_eq_right (show ¬ IsCoprime b a from fun hc => hab hc.symm)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideRadialOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved coprime operator majorant on the full compact norm range.
This keeps the actual quotient rows instead of assuming a thin dyad. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem wideCoprimeRadialForm_norm_le (M : ℝ) (hM : 0 < M) (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, 0 < x h)
    (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
      (∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖) *
        coprimeNormMajorant S H U v w := by
  have hc := wideGramMellinCoefficient_integrable M hM W hW hW' ρ
  have hi := hc.mul_bdd
    (coprimeMellinKernel_continuous S H v w phase x y).aestronglyMeasurable
    (Eventually.of_forall
      (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y))
  rw [wideCoprimeRadialForm_mellin M hM S H v w phase x y hx hy hlog W hW hW' hρ]
  calc
    _ ≤ ∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t *
        coprimeMellinKernel S H v w phase x y t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖ *
        coprimeNormMajorant S H U v w := by
      apply integral_mono hi.norm (hc.norm.mul_const _)
      intro t
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y t)
        (_root_.norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem wideCoprimeRadialForm_rapidDecay (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H U : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      (∀ p ∈ U, primaryPrime p) →
      (∀ a ∈ S, primaryPrimeFactors a ⊆ U) →
      ∀ (v w phase : Eisenstein → ℂ), (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      ∀ (x y : Eisenstein → ℝ),
      (∀ h ∈ H, 0 < x h) →
      (∀ a ∈ S, 0 < y a) →
      (∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
        C * coprimeNormMajorant S H U v w := by
  obtain ⟨C, hC, hc⟩ := wideGramMellinCoefficient_mass_rapidDecay M hM W hW hW' A
  refine ⟨C, hC, ?_⟩
  intro S H U hS hU hSU v w phase hphase x y hx hy hlog ρ hρ
  calc
    _ ≤ (1+ρ)^A * ((∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖) *
        coprimeNormMajorant S H U v w) :=
      mul_le_mul_of_nonneg_left
        (wideCoprimeRadialForm_norm_le M hM S H U hS hU hSU v w phase hphase x y hx hy hlog W hW hW' hρ)
        (by positivity)
    _ = ((1+ρ)^A * (∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖)) *
        coprimeNormMajorant S H U v w := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hc ρ hρ) (coprimeNormMajorant_nonneg _ _ _ _ _)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WidePoissonRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common-factor quotient rows retain a fixed compact norm range; the
wide Mellin operator bound supplies their exact Poisson recurrence. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem wide_coprimePoissonDyad_norm_recurrence (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (u : Eisenstein → ℂ) (Z J N : ℝ), 0 ≤ Z → 0 < J → 0 < N →
      (∀ a ∈ S, N ≤ norm a) →
      (∀ h ∈ H, 0 < norm h) →
      (∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S,
        |Real.log (norm h/J)-Real.log ((norm a/N)*(norm b/N))| ≤ M) →
      (1+Z*J/(27*N^2))^A * ‖coprimePoissonDyad S H u W Z‖ ≤
        C*(Z/N)*finiteCubicBound S H *
          ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := wideCoprimeRadialForm_rapidDecay M hM W hW hW' A
  refine ⟨C/9, by positivity, ?_⟩
  intro S H hS u Z J N hZ hJ hN hSN hHJ hlog
  let U := sievePrimeSet S
  have hU : ∀ p ∈ U, primaryPrime p := sievePrimeSet_primary S (fun a ha => (hS a ha).1)
  have hu : ∀ a ∈ S, primaryPrimeFactors a ⊆ U := fun a ha => factors_subset_sievePrimeSet ha
  have hx : ∀ h ∈ H, 0 < norm h/J := fun h hh => div_pos (hHJ h hh) hJ
  have hy : ∀ a ∈ S, 0 < norm a/N := fun a ha => div_pos (hN.trans_le (hSN a ha)) hN
  have hi := hbound S H U hS hU hu (gaussRowCoefficient u) (gaussRowCoefficient u)
    (fun h => (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ))
    (fun h hh => by simp only [Circle.norm_coe, le_refl])
    (fun h => norm h/J) (fun a => norm a/N) hx hy hlog (Z*J/(27*N^2)) (by positivity)
  have hmajor : coprimeNormMajorant S H U (gaussRowCoefficient u) (gaussRowCoefficient u) ≤
      finiteCubicBound S H *
        ((∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2)/N) := by
    calc
      _ ≤ finiteCubicBound S H *
          ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖gaussRowCoefficient u a‖^2 := by
        convert coprimeNormMajorant_le_divisorEnergy S H U (fun a ha => (hS a ha).1)
          hU (gaussRowCoefficient u) (gaussRowCoefficient u) using 1
        all_goals try with_reducible_and_instances rfl
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (gaussRowCoefficient_divisor_energy S hS u hN hSN)
        (finiteCubicBound_nonneg _ _)
  rw [coprimePoissonDyad_separated S H u W hZ (ne_of_gt hJ) (ne_of_gt hN),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ = (Z/9) * ((1+Z*J/(27*N^2))^A * ‖coprimeRadialForm S H
        (gaussRowCoefficient u) (gaussRowCoefficient u)
        (fun h => (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ))
        (fun h => norm h/J) (fun a => norm a/N) W (Z*J/(27*N^2))‖) := by ring
    _ ≤ (Z/9) * (C*(finiteCubicBound S H *
        ((∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2)/N))) :=
      mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hmajor hC.le)) (by positivity)
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeZeroMode
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Keep the zero frequency explicitly when a common-factor quotient
contains the unit row. No nonunit assumption is imposed on that support. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma hasSum_frequencyDyad_sub_zero (F : Eisenstein → ℂ) (hF : Summable F) :
    HasSum (fun j : ℕ => ∑ h ∈ frequencyDyad j, F h) ((∑' h, F h)-F 0) := by
  have hs : HasSum (fun h : Eisenstein => if h = 0 then 0 else F h) ((∑' h, F h)-F 0) :=
    hasSum_ite_sub_hasSum hF.hasSum 0
  have hd := hasSum_frequencyDyad _ hs.summable (by simp)
  rw [hs.tsum_eq] at hd
  apply hd.congr_fun
  intro j
  apply Finset.sum_congr rfl
  intro h hh
  exact (ite_eq_right (mem_frequencyDyad.mp hh).1).symm

lemma coprimeGramForm_poisson_all (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    HasSum (fun h : Eisenstein => coprimePoissonDyad S {h} u W Z) (coprimeGramForm S u W Z) := by
  unfold coprimePoissonDyad coprimeGramForm
  simp only [Finset.sum_singleton]
  apply hasSum_sum
  intro a ha
  apply hasSum_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    have hs := (summable_gramDualTerm (hS a ha).1 (hS b hb).1 W hW hW' hZ).hasSum.mul_left
      (u a*star (u b)*(Z/(9*Real.sqrt (norm (a*b))):ℝ)*(gauss a*star (gauss b)))
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    rw [primaryCharacterGram_poisson_normalized (hS a ha).1 (hS b hb).1
      (hS a ha).2 (hS b hb).2 hab W hW hW' hZ]
    ring
  · simp only [ite_eq_right hab]
    exact hasSum_zero

 theorem hasSum_coprimePoissonDyad_with_zero (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    HasSum (fun j : ℕ => coprimePoissonDyad S (frequencyDyad j) u W Z)
      (coprimeGramForm S u W Z-coprimePoissonDyad S {0} u W Z) := by
  have hs := coprimeGramForm_poisson_all S hS u W hW hW' hZ
  have hd := hasSum_frequencyDyad_sub_zero _ hs.summable
  rw [hs.tsum_eq] at hd
  apply hd.congr_fun
  intro j
  symm
  unfold coprimePoissonDyad
  simp only [Finset.sum_singleton]
  simp_rw [Finset.sum_comm (s := frequencyDyad j) (t := S)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,Finset.mul_sum]
  · simp only [ite_eq_right hab,Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeUnitFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterDyadicSum
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of all three outer-sieve powers at the true Poisson scale. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
open SevenEighths.CubicDyadicDecay

lemma finite_dyadic_power_decay (I : Finset ℕ) {t α : ℝ}
    (ht : 0 < t) (hα : 0 < α) (hα3 : α < 3) :
    (∑ j ∈ I, ((2:ℝ)^j)^α/(1+t*2^j)^3) ≤ SevenEighths.CubicDyadicDecay.decayConstant α*t^(-α) := by
  exact ((decay_summable t α ht hα3).sum_le_tsum I (fun j _ => by positivity)).trans
    (dyadic_decay_bound t α ht hα hα3)

lemma sum_outer_dyadic_envelope (I : Finset ℕ) {ε N t : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 0 ≤ N) (ht : 0 < t) :
    (∑ j ∈ I, ((2:ℝ)^j)^ε *
      ((2:ℝ)^j+((2:ℝ)^j*N)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*N)/(1+t*2^j)^3) ≤
      outerDyadicBound ε N t := by
  have hp (j : ℕ) : ((2:ℝ)^j)^ε *
      ((2:ℝ)^j+((2:ℝ)^j*N)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*N)/(1+t*2^j)^3 =
      ((2:ℝ)^j)^(ε+1)/(1+t*2^j)^3+
      N^(2/3:ℝ)*(((2:ℝ)^j)^(ε+2/3)/(1+t*2^j)^3)+
      N*(((2:ℝ)^j)^(ε+1/3)/(1+t*2^j)^3) := by
    rw [Real.mul_rpow (by positivity) hN,Real.rpow_add (by positivity),
      Real.rpow_add (by positivity),Real.rpow_add (by positivity),Real.rpow_one]
    ring
  simp_rw [hp,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  simpa only [outerDyadicBound,mul_assoc] using add_le_add (add_le_add
    (finite_dyadic_power_decay (α := ε+1) I ht (by linarith) (by linarith))
    (mul_le_mul_of_nonneg_left (finite_dyadic_power_decay (α := ε+2/3) I ht (by linarith) (by linarith))
      (Real.rpow_nonneg hN _)))
    (mul_le_mul_of_nonneg_left (finite_dyadic_power_decay (α := ε+1/3) I ht (by linarith) (by linarith)) hN)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterPoissonAnnulus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coprime Poisson annulus, including cube frequencies,
for the compact norm interval of a common-factor quotient. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
namespace CubicFirstMoment

 theorem coprime_poisson_outer_annulus {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ) (j : ℕ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ R*N) →
      (1+Z*2^j/(27*N^2))^3 * ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ ≤
        C*(Z/N)*(4*2^j*(R*N))^ε*
          (2*2^j+(2*2^j*(R*N))^(2/3:ℝ)+(2*2^j)^(1/3:ℝ)*(R*N))*
            ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  have hM : 0 < 1+2*Real.log R := by linarith [Real.log_nonneg hR]
  obtain ⟨C₁,hC₁,hrec⟩ := wide_coprimePoissonDyad_norm_recurrence
    (1+2*Real.log R) hM W hW hW' 3
  obtain ⟨C₂,hC₂,houter⟩ := all_frequency_cubic_operator_bound hε
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro S u Z N j hZ hN hS
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hJ : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hs : ∀ a ∈ S, primary a ∧ Squarefree a :=
    fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hlog : ∀ h ∈ frequencyDyad j, ∀ a ∈ S, ∀ b ∈ S,
      |Real.log (norm h/2^j)-Real.log ((norm a/N)*(norm b/N))| ≤ 1+2*Real.log R := by
    intro h hh a ha b hb
    apply compact_norm_log_ratio hR
    · exact ⟨(le_div_iff₀ (by positivity : (0:ℝ) < 2^j)).mpr
        (by simpa only [one_mul] using (frequencyDyad_norm hh).1),
        (div_le_iff₀ (by positivity : (0:ℝ) < 2^j)).mpr (frequencyDyad_norm hh).2⟩
    · exact ⟨(le_div_iff₀ hNp).mpr (by simpa only [one_mul] using (hS a ha).2.2.1),
        (div_le_iff₀ hNp).mpr (hS a ha).2.2.2⟩
    · exact ⟨(le_div_iff₀ hNp).mpr (by simpa only [one_mul] using (hS b hb).2.2.1),
        (div_le_iff₀ hNp).mpr (hS b hb).2.2.2⟩
  have hr := hrec S (frequencyDyad j) hs u Z (2^j) N hZ.le (by positivity) hNp
    (fun a ha => (hS a ha).2.2.1)
    (fun h hh => (by positivity : (0:ℝ) < 2^j).trans_le (frequencyDyad_norm hh).1) hlog
  have hb := houter S (frequencyDyad j) (2*2^j) (R*N) (by nlinarith) (by nlinarith)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)
    (fun h hh => ⟨(mem_frequencyDyad.mp hh).1,(frequencyDyad_norm hh).2⟩)
  apply hr.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ C₁*(Z/N))) (Finset.sum_nonneg (fun _ _ => by positivity))).trans_eq
  congr 1
  rw [show 2*(2*2^j)*(R*N) = 4*2^j*(R*N) by ring]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterScale
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical summation of the common-factor outer sieve at the exact
Poisson frequency scale. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma outer_scaled_envelope {J T ε : ℝ} (hJ : 0 < J) (hT : 0 ≤ T) :
    (4*J*T)^ε*(2*J+(2*J*T)^(2/3:ℝ)+(2*J)^(1/3:ℝ)*T) ≤
      2*(4*T)^ε*J^ε*(J+(J*T)^(2/3:ℝ)+J^(1/3:ℝ)*T) := by
  have h2 : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (2/3:ℝ) ≤ 1)
  have h1 : (2:ℝ)^(1/3:ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (1/3:ℝ) ≤ 1)
  have heq : (4*J*T)^ε = (4*T)^ε*J^ε := by
    rw [show 4*J*T = (4*T)*J by ring,Real.mul_rpow (by positivity) hJ.le]
  rw [heq,show 2*J*T = 2*(J*T) by ring,
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hJ.le hT),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hJ.le]
  have hp : 2*J+2^(2/3:ℝ)*(J*T)^(2/3:ℝ)+2^(1/3:ℝ)*J^(1/3:ℝ)*T ≤
      2*(J+(J*T)^(2/3:ℝ)+J^(1/3:ℝ)*T) := by
    have hp2 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (mul_nonneg hJ.le hT) (2/3))
    have hp1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hJ.le (1/3))) hT
    linarith
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring)

lemma finite_outer_poisson_sum (I : Finset ℕ) (F : ℕ → ℂ)
    {C Z N T ε : ℝ} (hC : 0 ≤ C) (hZ : 0 < Z) (hN : 0 < N) (hT : 0 ≤ T)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hF : ∀ j ∈ I, (1+Z*2^j/(27*N^2))^3*‖F j‖ ≤
      C*(Z/N)*(4*2^j*T)^ε*
        (2*2^j+(2*2^j*T)^(2/3:ℝ)+(2*2^j)^(1/3:ℝ)*T)) :
    ‖∑ j ∈ I, F j‖ ≤
      (2*C*(Z/N)*(4*T)^ε)*outerDyadicBound ε T (Z/(27*N^2)) := by
  let t := Z/(27*N^2)
  have ht : 0 < t := by dsimp [t]; positivity
  let K := 2*C*(Z/N)*(4*T)^ε
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hj (j : ℕ) (hj : j ∈ I) : ‖F j‖ ≤
      K*(((2:ℝ)^j)^ε*((2:ℝ)^j+((2:ℝ)^j*T)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*T)/
        (1+t*2^j)^3) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < (1+t*2^j)^3)).mpr
    have hstart := hF j hj
    rw [mul_assoc (C*(Z/N))] at hstart
    have hh := hstart.trans
      (mul_le_mul_of_nonneg_left (outer_scaled_envelope (ε := ε) (by positivity : (0:ℝ) < 2^j) hT)
        (by positivity : 0 ≤ C*(Z/N)))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [t,K] <;> ring)
  calc
    _ ≤ ∑ j ∈ I, ‖F j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ I, K*(((2:ℝ)^j)^ε*((2:ℝ)^j+
        ((2:ℝ)^j*T)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*T)/(1+t*2^j)^3) :=
      Finset.sum_le_sum hj
    _ = K*∑ j ∈ I, ((2:ℝ)^j)^ε*((2:ℝ)^j+
        ((2:ℝ)^j*T)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*T)/(1+t*2^j)^3 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_outer_dyadic_envelope I hε hε1 hT ht) hK

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterDualBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of every dual frequency in the common-factor Gram kernel,
with the unit zero mode explicitly subtracted. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment

 theorem coprimeGramForm_outer_dual_bound {ε R : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hR : 1 ≤ R) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ R*N) →
      ‖coprimeGramForm S u W Z-coprimePoissonDyad S {0} u W Z‖ ≤
        (2*C*(Z/N)*(4*(R*N))^ε)*outerDyadicBound ε (R*N) (Z/(27*N^2))*
          ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprime_poisson_outer_annulus hε hR W hW hW'
  refine ⟨C,hC,?_⟩
  intro S u Z N hZ hN hS
  let E := ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => by positivity)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hR0 : 0 ≤ R*N := mul_nonneg (zero_le_one.trans hR) hNp.le
  have hfinite (I : Finset ℕ) :
      ‖∑ j ∈ I, coprimePoissonDyad S (frequencyDyad j) u W Z‖ ≤
        (2*C*(Z/N)*(4*(R*N))^ε)*outerDyadicBound ε (R*N) (Z/(27*N^2))*E := by
    have hf (j : ℕ) (_ : j ∈ I) := hbound S u Z N j hZ hN hS
    have hh := finite_outer_poisson_sum I
      (fun j => coprimePoissonDyad S (frequencyDyad j) u W Z)
      (C := C*E) (T := R*N) (ε := ε) (mul_nonneg hC.le hE) hZ hNp hR0 hε hε1
      (fun j hj => (hf j hj).trans_eq (by dsimp only [E]; ring))
    exact hh.trans_eq (by ring)
  have hs := hasSum_coprimePoissonDyad_with_zero S
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) u W hW hW' hZ
  exact le_of_tendsto hs.norm (Eventually.of_forall hfinite)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterPowerScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore the primal powers after summing at the dual Poisson scale. -/
noncomputable section
namespace CubicFirstMoment

lemma outer_poisson_power_scale {Z N R : ℝ} (hZ : 0 < Z) (hN : 0 < N)
    (hR : 0 < R) (ε α β : ℝ) :
    (Z/N)*(4*R*N)^ε*(R*N)^β*(Z/(27*N^2))^(-α) =
      (4*R)^ε*R^β*27^α*Z^(1-α)*N^(ε+β+2*α-1) := by
  have ht : (Z/(27*N^2))^(-α) = 27^α*N^(2*α)/Z^α := by
    rw [Real.rpow_neg (by positivity : 0 ≤ Z/(27*N^2)),
      Real.div_rpow hZ.le (by positivity : 0 ≤ 27*N^2),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 27) (sq_nonneg N),inv_div,
      ← Real.rpow_natCast N 2,← Real.rpow_mul hN.le]
    norm_num
  have hz : Z^(1-α) = Z/Z^α := by rw [Real.rpow_sub hZ,Real.rpow_one]
  have hn : N^(ε+β+2*α-1) = N^ε*N^β*N^(2*α)/N := by
    rw [Real.rpow_sub hN,Real.rpow_add hN,Real.rpow_add hN,Real.rpow_one]
  rw [ht,hz,hn,Real.mul_rpow (by positivity : 0 ≤ 4*R) hN.le,
    Real.mul_rpow hR.le hN.le]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterPrimalScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the three primal powers from the exact summed Poisson bound.
The epsilon loss does not multiply the separate unit zero-frequency term. -/
noncomputable section
namespace CubicFirstMoment

lemma outer_poisson_power_common {Z N R : ℝ} (hZ : 0 < Z) (hN : 0 < N)
    (hR : 0 < R) (ε α β : ℝ) :
    (Z/N)*(4*R*N)^ε*(R*N)^β*(Z/(27*N^2))^(-(ε+α)) =
      (4*R)^ε*R^β*27^(ε+α)*(N^3/Z)^ε*Z^(1-α)*N^(β+2*α-1) := by
  rw [outer_poisson_power_scale hZ hN hR]
  have hp : (N^3/Z)^ε = N^(3*ε)/Z^ε := by
    rw [Real.div_rpow (by positivity) hZ.le,← Real.rpow_natCast N 3,
      ← Real.rpow_mul hN.le]
    norm_num
  have hz : Z^(1-(ε+α)) = Z^(1-α)/Z^ε := by
    rw [show 1-(ε+α) = (1-α)-ε by ring,Real.rpow_sub hZ]
  have hn : N^(ε+β+2*(ε+α)-1) = N^(3*ε)*N^(β+2*α-1) := by
    rw [show ε+β+2*(ε+α)-1 = 3*ε+(β+2*α-1) by ring,Real.rpow_add hN]
  rw [hp,hz,hn]
  ring

lemma outerPowerConstant_pos {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) : 0 < outerPowerConstant ε R := by
  have h1 := SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1) (by linarith) (by linarith)
  have h2 := SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+2/3) (by linarith) (by linarith)
  have h3 := SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1/3) (by linarith) (by linarith)
  unfold outerPowerConstant
  positivity

lemma outer_primal_scale_bound {Z N R C ε : ℝ} (hZ : 0 < Z) (hN : 0 < N)
    (hR : 0 < R) (hC : 0 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (2*C*(Z/N)*(4*(R*N))^ε)*outerDyadicBound ε (R*N) (Z/(27*N^2)) ≤
      C*outerPowerConstant ε R*(N^3/Z)^ε*
        (N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ)) := by
  let d₁ := SevenEighths.CubicDyadicDecay.decayConstant (ε+1)*27^(ε+1)
  let d₂ := R^(2/3:ℝ)*SevenEighths.CubicDyadicDecay.decayConstant (ε+2/3)*27^(ε+2/3)
  let d₃ := R*SevenEighths.CubicDyadicDecay.decayConstant (ε+1/3)*27^(ε+1/3)
  have hd₁ : 0 ≤ d₁ := mul_nonneg
    (SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1) (by linarith) (by linarith)).le
    (by positivity)
  have hd₂ : 0 ≤ d₂ := mul_nonneg (mul_nonneg (by positivity)
    (SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+2/3) (by linarith) (by linarith)).le)
    (by positivity)
  have hd₃ : 0 ≤ d₃ := mul_nonneg (mul_nonneg hR.le
    (SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1/3) (by linarith) (by linarith)).le)
    (by positivity)
  have h1 := outer_poisson_power_common hZ hN hR ε 1 0
  have h2 := outer_poisson_power_common hZ hN hR ε (2/3) (2/3)
  have h3 := outer_poisson_power_common hZ hN hR ε (1/3) 1
  norm_num at h1 h2 h3
  have heq : (2*C*(Z/N)*(4*(R*N))^ε)*outerDyadicBound ε (R*N) (Z/(27*N^2)) =
      2*C*(4*R)^ε*(N^3/Z)^ε*
        (d₁*N+d₂*(Z^(1/3:ℝ)*N)+d₃*(Z^(2/3:ℝ)*N^(2/3:ℝ))) := by
    unfold outerDyadicBound
    rw [show 4*(R*N) = 4*R*N by ring]
    calc
      _ = 2*C*(SevenEighths.CubicDyadicDecay.decayConstant (ε+1)*
          ((Z/N)*(4*R*N)^ε*(Z/(27*N^2))^(-(ε+1))) +
        SevenEighths.CubicDyadicDecay.decayConstant (ε+2/3)*
          ((Z/N)*(4*R*N)^ε*(R*N)^(2/3:ℝ)*(Z/(27*N^2))^(-(ε+2/3))) +
        SevenEighths.CubicDyadicDecay.decayConstant (ε+1/3)*
          ((Z/N)*(4*R*N)^ε*(R*N)*(Z/(27*N^2))^(-(ε+1/3)))) := by ring
      _ = _ := by simp only [neg_add_rev]; rw [h1,h2,h3]; dsimp [d₁,d₂,d₃]; ring
  rw [heq]
  have hb : d₁*N+d₂*(Z^(1/3:ℝ)*N)+d₃*(Z^(2/3:ℝ)*N^(2/3:ℝ)) ≤
      (d₁+d₂+d₃)*(N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ)) := by
    calc
      _ ≤ (d₁+d₂+d₃)*N+(d₁+d₂+d₃)*(Z^(1/3:ℝ)*N)+
          (d₁+d₂+d₃)*(Z^(2/3:ℝ)*N^(2/3:ℝ)) := by
        apply add_le_add
        · apply add_le_add <;> apply mul_le_mul_of_nonneg_right <;> first | positivity | linarith
        · apply mul_le_mul_of_nonneg_right <;> first | positivity | linarith
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by
    dsimp [outerPowerConstant,d₁,d₂,d₃]; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeOuterComplete
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All frequencies of the compact Gram kernel. Its zero mode has no
epsilon loss; the remaining frequencies have the three primal powers. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimePoissonDyad_zero_bound (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) :
    ‖coprimePoissonDyad S {0} u W Z‖ ≤
      (‖normProfileFourier W 0‖/9)*Z*
        ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  rw [coprimePoissonDyad_unit_frequency S hS]
  by_cases h1 : (1:Eisenstein) ∈ S
  · rw [ite_eq_left h1,norm_mul,norm_mul,norm_mul,norm_star,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < Z/9)]
    have he : ‖u 1‖^2 ≤ ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
      calc
        ‖u 1‖^2 ≤ (2:ℝ)^(primaryPrimeFactors 1).card*‖u 1‖^2 :=
          le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (by norm_num))
        _ ≤ _ := Finset.single_le_sum
          (f := fun a => (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2)
          (fun a ha => mul_nonneg (by positivity) (sq_nonneg _)) h1
    calc
      _ = (‖normProfileFourier W 0‖/9)*Z*‖u 1‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
  · rw [ite_eq_right h1,norm_zero]
    positivity

 theorem coprimeGramForm_outer_complete {ε R : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hR : 1 ≤ R) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ R*N) →
      ‖coprimeGramForm S u W Z‖ ≤
        ((‖normProfileFourier W 0‖/9)*Z + C*(N^3/Z)^ε*
          (N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ)))*
            ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprimeGramForm_outer_dual_bound hε hε1 hR W hW hW'
  have hRp : 0 < R := zero_lt_one.trans_le hR
  refine ⟨C*outerPowerConstant ε R,mul_pos hC (outerPowerConstant_pos hε hε1 hRp),?_⟩
  intro S u Z N hZ hN hS
  have hE : 0 ≤ ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hd := (hbound S u Z N hZ hN hS).trans
    (mul_le_mul_of_nonneg_right
      (outer_primal_scale_bound hZ (zero_lt_one.trans_le hN) hRp hC.le hε hε1) hE)
  have hz := coprimePoissonDyad_zero_bound S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
    u W hZ
  have hh := norm_add_le (coprimeGramForm S u W Z-coprimePoissonDyad S {0} u W Z)
    (coprimePoissonDyad S {0} u W Z)
  rw [sub_add_cancel] at hh
  exact hh.trans ((add_le_add hd hz).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterCostMonotone
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformize the three primal powers without attaching an epsilon
loss to the zero-frequency A term. -/
noncomputable section
namespace CubicFirstMoment

lemma outer_cost_mono {ε C K Z A N M P : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hK : 0 ≤ K) (hZ : 0 < Z)
    (hZA : Z ≤ A) (hN : 0 ≤ N) (hNM : N ≤ M) (hP : N^3/Z ≤ P) :
    K*Z+C*(N^3/Z)^ε*(N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ)) ≤
      K*A+C*P^ε*(M+A^(1/3:ℝ)*M+A^(2/3:ℝ)*M^(2/3:ℝ)) := by
  have hA0 : 0 ≤ A := hZ.le.trans hZA
  have hM0 : 0 ≤ M := hN.trans hNM
  have hP0 : 0 ≤ P := (div_nonneg (pow_nonneg hN 3) hZ.le).trans hP
  apply add_le_add (mul_le_mul_of_nonneg_left hZA hK)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hP hε) hC
  · apply add_le_add
    · exact add_le_add hNM (mul_le_mul
        (Real.rpow_le_rpow hZ.le hZA (by norm_num)) hNM hN (by positivity))
    · exact mul_le_mul (Real.rpow_le_rpow hZ.le hZA (by norm_num))
        (Real.rpow_le_rpow hN hNM (by norm_num)) (by positivity) (by positivity)
  · positivity
  · positivity

lemma quotient_scale_bound {A L Q D B m k : ℝ}
    (hA : 0 < A) (hL : 1 ≤ L) (hQ : 1 ≤ Q) (hD : 1 ≤ D)
    (hk : 1 ≤ k) (hkm : m ≤ k) (hm : 1 ≤ m) (hkL : k ≤ B*L)
    (hB : 1 ≤ B) (hkD : D ≤ k) :
    let Z := A/Q^2/m
    let N := max 1 (L/k)
    0 < Z ∧ 1 ≤ N ∧ Z ≤ A ∧ N ≤ max 1 (L/D) ∧
      N^3/Z ≤ B*Q^2*L^3/A := by
  dsimp only
  have hAp := hA
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hkp : 0 < k := zero_lt_one.trans_le hk
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hmp : 0 < m := zero_lt_one.trans_le hm
  have hZ : 0 < A/Q^2/m := by positivity
  refine ⟨hZ,le_max_left _ _,?_,?_,?_⟩
  · calc
      A/Q^2/m ≤ A/Q^2 := div_le_self (by positivity) hm
      _ ≤ A := div_le_self hA.le (one_le_pow₀ hQ)
  · exact max_le_max_left _ (div_le_div_of_nonneg_left hLp.le hDp hkD)
  · have hp : (max 1 (L/k))^3*m ≤ B*L^3 := by
      by_cases hkL' : k ≤ L
      · rw [max_eq_right ((le_div_iff₀ hkp).mpr (by simpa using hkL'))]
        have hk3 : k ≤ k^3 := le_self_pow₀ hk (by norm_num : (3:ℕ) ≠ 0)
        calc
          (L/k)^3*m ≤ (L/k)^3*k^3 :=
            mul_le_mul_of_nonneg_left (hkm.trans hk3) (by positivity)
          _ = L^3 := by field_simp
          _ ≤ B*L^3 := le_mul_of_one_le_left (by positivity) hB
      · rw [max_eq_left ((div_le_one hkp).mpr (le_of_not_ge hkL'))]
        norm_num only [one_pow,one_mul]
        have hL3 : L ≤ L^3 := le_self_pow₀ hL (by norm_num : (3:ℕ) ≠ 0)
        exact hkm.trans (hkL.trans (mul_le_mul_of_nonneg_left hL3 (zero_le_one.trans hB)))
    rw [show (max 1 (L/k))^3/(A/Q^2/m) =
      ((max 1 (L/k))^3*m)*Q^2/A by field_simp]
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hp (sq_nonneg Q)).trans_eq (by ring)) hA.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCubeRoughness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit reciprocal-prime error in the cube lattice saves a
power on every rough fixed-length prime convolution. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeProduct_primeFactors_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) :
    (primaryPrimeFactors b).card ≤ Fintype.card ι := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  have hp (i : ι) : primaryPrime (f i) := hS i _ (Fintype.mem_piFinset.mp hf i)
  have hprim : primary (∏ i, f i) := primary_finset_prod _ _ (fun i _ => (hp i).1)
  have hsub : primaryPrimeFactors (∏ i, f i) ⊆ Finset.univ.image f := by
    intro p hmem
    have hpp := (primaryPrimeFactor_spec hprim hmem).1
    have hpd := (primaryPrimeFactor_spec hprim hmem).2
    obtain ⟨i,_,hi⟩ := (hpp.2.dvd_finsetProd_iff f).mp hpd
    have he : p = f i := primary_associated_eq hpp.1 (hp i).1
      ((hpp.2.dvd_prime_iff_associated (hp i).2).mp hi)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩
  exact (Finset.card_le_card hsub).trans (by simpa using Finset.card_image_le (s := (Finset.univ:Finset ι)) (f := f))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCommonRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic bounds for the actual common-factor quotient rows. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrime_nonunit_common_factor_large {R D : ℝ}
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) {k : Eisenstein}
    (hk : k ∈ commonRowFactors (fullSquarefreePrimeSupport R W X e)) (hk1 : k ≠ 1) :
    D < norm k := by
  have hS : ∀ a ∈ fullSquarefreePrimeSupport R W X e, primary a ∧ Squarefree a :=
    fun a ha => fullSquarefreePrimeSupport_primary R W X e ha
  have hks := commonRowFactors_spec hS hk
  have hpnonempty : (primaryPrimeFactors k).Nonempty := by
    by_contra hn
    have he := primaryPrimeFactors_prod hks.1 hks.2
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.prod_empty] at he
    exact hk1 he.symm
  obtain ⟨⟨a,b⟩,hab,hprod⟩ := Finset.mem_image.mp hk
  have ha := (Finset.mem_product.mp hab).1
  have hb := (Finset.mem_product.mp hab).2
  have hkd : k ∣ a := hprod ▸
    (primaryCommonFactor_spec (hS a ha).1 (hS b hb).1 (hS a ha).2 (hS b hb).2).2.2.1
  have hprodK := primaryPrimeFactors_prod hks.1 hks.2
  rw [← hprodK]
  exact fullPrime_nonempty_divisor_large W X hX hlo hhi hrough (primaryPrimeFactors k)
    (fun p hp => (primaryPrimeFactor_spec hks.1 hp).1) hpnonempty
    (Finset.mem_filter.mp ha).1 (hprodK.symm ▸ hkd)

lemma fullPrime_common_energy_bound (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (v : Eisenstein → ℂ) :
    (∑ k ∈ commonRowFactors (fullSquarefreePrimeSupport R W X e),
      (2:ℝ)^(primaryPrimeFactors k).card *
        commonBlockEnergy (fullSquarefreePrimeSupport R W X e) v k) ≤
      (2:ℝ)^(3*Fintype.card ι) *
        ∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖v a‖^2 := by
  have hS : ∀ a ∈ fullSquarefreePrimeSupport R W X e, primary a ∧ Squarefree a :=
    fun a ha => fullSquarefreePrimeSupport_primary R W X e ha
  apply (common_energy_cubic_weight _ hS v).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hc : (primaryPrimeFactors a).card ≤ Fintype.card ι :=
    primeProduct_primeFactors_card _ (fullPrimeSupport_prime R W X) (Finset.mem_filter.mp ha).1
  rw [← pow_mul]
  apply pow_le_pow_right₀ (by norm_num)
  omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonOuterBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform bound for the actual shortened common-factor rows. The
roughness threshold enters their lengths, rather than a new hypothesis
about character cancellation. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma commonOuterCost_nonneg (W : ℝ → ℂ) {C ε B Q A L D : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    0 ≤ commonOuterCost W C ε B Q A L D := by
  unfold commonOuterCost
  positivity

 theorem commonGramBlock_outer_bound {ε B : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : 1 ≤ B) (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Q A L D : ℝ),
      1 ≤ Q → 0 < A → 1 ≤ L → 1 ≤ D →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ L ≤ norm a ∧ norm a ≤ B*L) →
      ∀ k ∈ commonRowFactors S, D ≤ norm k →
      ‖commonGramBlock S u W (A/Q^2) k‖ ≤
        (2:ℝ)^(primaryPrimeFactors k).card*commonOuterCost W C ε B Q A L D*
          commonBlockEnergy S u k := by
  obtain ⟨C,hC,hbound⟩ := coprimeGramForm_outer_complete hε hε1 hB W hW hW'
  refine ⟨C,hC,?_⟩
  intro S u Q A L D hQ hA hL hD hS k hkS hkD
  have hS' : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hk := commonRowFactors_spec hS' hkS
  have hk0 := primary_ne_zero hk.1
  have hkN := norm_pos_of_ne_zero hk0
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hr := residualRows_primary hk.1 hS'
  have hkBL : norm k ≤ B*L := by
    obtain ⟨⟨a,b⟩,hab,hkab⟩ := Finset.mem_image.mp hkS
    have ha := (Finset.mem_product.mp hab).1
    have hb := (Finset.mem_product.mp hab).2
    have hd : k ∣ a := hkab ▸
      (primaryCommonFactor_spec (hS a ha).1 (hS b hb).1 (hS a ha).2.1 (hS b hb).2.1).2.2.1
    exact (norm_le_of_dvd (primary_ne_zero (hS a ha).1) hd).trans (hS a ha).2.2.2
  have hrows : ∀ a ∈ residualRows S k,
      primary a ∧ Squarefree a ∧ max 1 (L/norm k) ≤ norm a ∧ norm a ≤ B*max 1 (L/norm k) := by
    intro a ha
    have hka := hS (k*a) ((mem_residualRows hk0).mp ha)
    have hlo : L/norm k ≤ norm a := (div_le_iff₀ hkN).mpr (by
      simpa only [norm_mul_eq,mul_comm] using hka.2.2.1)
    have hhi : norm a ≤ B*(L/norm k) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hkN).mpr
      simpa only [norm_mul_eq,mul_div_assoc,mul_comm] using hka.2.2.2
    exact ⟨(hr a ha).1,(hr a ha).2,
      max_le (one_le_norm (primary_ne_zero (hr a ha).1)) hlo,
      hhi.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (zero_le_one.trans hB))⟩
  rw [commonGramBlock_moebius S hS' u W hW hW' (by positivity) hk.1 hk.2]
  have heach (s : Finset Eisenstein) (hs : s ∈ (primaryPrimeFactors k).powerset) :
      ‖(idealMoebius (∏ p ∈ s,p):ℂ)*coprimeGramForm (residualRows S k)
        (commonBlockCoefficient u k (∏ p ∈ s,p)) W (A/Q^2/norm (∏ p ∈ s,p))‖ ≤
      commonOuterCost W C ε B Q A L D*commonBlockEnergy S u k := by
    let m := ∏ p ∈ s,p
    have hm : primary m := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).1.1)
    have hmk : m ∣ k := (primary_subsets_prod_dvd hk.1 (Finset.mem_powerset.mp hs) k).mpr
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).2)
    have hscale := quotient_scale_bound hA hL hQ hD (one_le_norm hk0)
      (norm_le_of_dvd hk0 hmk) (one_le_norm (primary_ne_zero hm)) hkBL hB hkD
    have hh := hbound (residualRows S k) (commonBlockCoefficient u k m)
      (A/Q^2/norm m) (max 1 (L/norm k)) hscale.1 hscale.2.1 hrows
    have hcost := outer_cost_mono hε.le hC.le (by positivity : 0 ≤ ‖normProfileFourier W 0‖/9)
      hscale.1 hscale.2.2.1 (by positivity : 0 ≤ max 1 (L/norm k)) hscale.2.2.2.1 hscale.2.2.2.2
    calc
      _ ≤ ‖coprimeGramForm (residualRows S k) (commonBlockCoefficient u k m)
          W (A/Q^2/norm m)‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one m)
      _ ≤ _ := hh.trans ((mul_le_mul_of_nonneg_right hcost
        (Finset.sum_nonneg (fun _ _ => by positivity))).trans
        (mul_le_mul_of_nonneg_left (commonBlockCoefficient_energy_le S hS' u hk.1 m)
          (commonOuterCost_nonneg W hC.le (zero_le_one.trans hB) hA.le (zero_le_one.trans hL))))
  calc
    _ ≤ ∑ s ∈ (primaryPrimeFactors k).powerset,
        ‖(idealMoebius (∏ p ∈ s,p):ℂ)*coprimeGramForm (residualRows S k)
          (commonBlockCoefficient u k (∏ p ∈ s,p)) W (A/Q^2/norm (∏ p ∈ s,p))‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ (primaryPrimeFactors k).powerset,
        commonOuterCost W C ε B Q A L D*commonBlockEnergy S u k := Finset.sum_le_sum heach
    _ = _ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonRemainderBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bound the noncoprime remainder by the energy of the genuine
common-factor blocks, and then by the original prime-convolution energy. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem primaryMass_sub_coprime_outer {ε B : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : 1 ≤ B) (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Q A L D : ℝ),
      1 ≤ Q → 0 < A → 1 ≤ L → 1 ≤ D →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ L ≤ norm a ∧ norm a ≤ B*L) →
      (∀ k ∈ commonRowFactors S, k ≠ 1 → D ≤ norm k) →
      ‖primarySmoothedSieveMass S u W (A/Q^2)-coprimeGramForm S u W (A/Q^2)‖ ≤
        commonOuterCost W C ε B Q A L D*
          ∑ k ∈ commonRowFactors S, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S u k := by
  obtain ⟨C,hC,hbound⟩ := commonGramBlock_outer_bound hε hε1 hB W hW hW'
  refine ⟨C,hC,?_⟩
  intro S u Q A L D hQ hA hL hD hS hrough
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hcost : 0 ≤ commonOuterCost W C ε B Q A L D :=
    commonOuterCost_nonneg W hC.le (zero_le_one.trans hB) hA.le (zero_le_one.trans hL)
  rw [primaryMass_sub_coprime_common S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
    u W hW hW' (by positivity)]
  calc
    _ ≤ ∑ k ∈ (commonRowFactors S).filter (· ≠ 1), ‖commonGramBlock S u W (A/Q^2) k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ (commonRowFactors S).filter (· ≠ 1),
        (2:ℝ)^(primaryPrimeFactors k).card*commonOuterCost W C ε B Q A L D*commonBlockEnergy S u k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hbound S u Q A L D hQ hA hL hD hS k (Finset.mem_filter.mp hk).1
        (hrough k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2)
    _ = commonOuterCost W C ε B Q A L D*
        ∑ k ∈ (commonRowFactors S).filter (· ≠ 1),
          (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S u k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun k hk hk' => mul_nonneg (by positivity)
        (commonBlockEnergy_nonneg S u k))) hcost

 theorem fullPrime_divisor_noncoprime_outer_oai {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 1 ≤ R)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (L D A : ℝ)
      (e d : Eisenstein) (β : Eisenstein → ℂ) (u : ℝ),
      (∀ i, 0 < X i) → (∏ i, X i) = L → 1 ≤ L → 1 ≤ D → 0 < A → primary d →
      (∀ i x, x < 1 → W i x = 0) → (∀ i x, R < x → W i x = 0) →
      (∀ i, D < X i) →
      ‖divisorDispersionVariance d (fullSquarefreePrimeSupport R W X e) β u V A-
        divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R W X e) β u V A‖ ≤
      commonOuterCost V C ε (R^Fintype.card ι) (norm d) A L D*
        (2:ℝ)^(3*Fintype.card ι)*
          ∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖β a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := primaryMass_sub_coprime_outer hε hε1
    (one_le_pow₀ hR) V hV hV'
  refine ⟨C,hC,?_⟩
  intro W X L D A e d β u hX hprod hL hD hA hd hlo hhi hrough
  let S := fullSquarefreePrimeSupport R W X e
  let v := divisorGramCoefficient d β u
  have hS : ∀ a ∈ S, primary a ∧ Squarefree a :=
    fun a ha => fullSquarefreePrimeSupport_primary R W X e ha
  have hSN : ∀ a ∈ S, primary a ∧ Squarefree a ∧ L ≤ norm a ∧ norm a ≤ R^Fintype.card ι*L := by
    intro a ha
    have hn := fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp ha).1
    rw [hprod] at hn
    exact ⟨(hS a ha).1,(hS a ha).2,hn⟩
  have hh := hbound S v (norm d) A L D (one_le_norm (primary_ne_zero hd)) hA hL hD hSN
    (fun k hk hk1 => (fullPrime_nonunit_common_factor_large W X hX hlo hhi hrough e hk hk1).le)
  rw [divisorDispersionVariance_eq_primaryMass hd S (fun a ha => (hS a ha).1) β u V hV hV' hA,
    divisorCoprimeDispersionGram_eq_coprimeGram]
  apply hh.trans
  have he := fullPrime_common_energy_bound R W X e v
  have he' : (∑ a ∈ S, ‖v a‖^2) ≤ ∑ a ∈ S, ‖β a‖^2 := by
    apply Finset.sum_le_sum
    intro a ha
    exact pow_le_pow_left₀ (_root_.norm_nonneg _)
      (divisorGramCoefficient_norm_le d β u (hS a ha).1) 2
  have henergy := he.trans (mul_le_mul_of_nonneg_left he' (by positivity))
  exact (mul_le_mul_of_nonneg_left henergy
    (commonOuterCost_nonneg V hC.le (by positivity) hA.le (zero_le_one.trans hL))).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer_oai.{u_1} := @OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer_oai.{u_1}
