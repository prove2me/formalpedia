-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_sieved_full_model_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:15:26.007965+00:00
-- url     : https://prove2.me/submissions/98b7dc36-d4cb-4f23-baf9-1b341ee9f726

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022
import Theorems.Thm_OAI_CubicFirstMoment_angular_divisor_noncube_total_saving
import Theorems.Thm_OAI_CubicFirstMoment_fullPrime_divisor_noncoprime_outer

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma norm_idealMoebius_le_one (m : Eisenstein) : ‖(idealMoebius m : ℂ)‖ ≤ 1 := by
  have hs : (idealMoebius m : ℝ)^2 ≤ 1 := by
    rw [idealMoebius_sq]
    split_ifs <;> norm_num
  have hn : ‖(idealMoebius m : ℂ)‖ = |(idealMoebius m : ℝ)| :=
    Complex.norm_intCast _
  rw [hn]
  nlinarith [sq_abs (idealMoebius m : ℝ), abs_nonneg (idealMoebius m : ℝ)]

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
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma dyadic_decay_step {c : ℝ} (hc : 0 < c) (j : ℕ) :
    (2 : ℝ)^j / (1+c*2^j)^2 ≤
      (2/c)*(1/(1+c*2^j)-1/(1+c*2^(j+1))) := by
  have hJ : 0 < (2 : ℝ)^j := by positivity
  have h1 : 0 < 1+c*2^j := by positivity
  have h2 : 0 < 1+2*c*2^j := by positivity
  calc
    _ ≤ 2*2^j / ((1+c*2^j)*(1+2*c*2^j)) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
      nlinarith [sq_nonneg (c*2^j),sq_nonneg ((2 : ℝ)^j), mul_pos hc hJ]
    _ = _ := by
      rw [pow_succ]
      have h2' : 1+c*((2 : ℝ)^j*2) ≠ 0 := by positivity
      field_simp
      ring

lemma dyadic_decay_partial_sum {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 : ℝ)^j/(1+c*2^j)^2) ≤ 2/c := by
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => dyadic_decay_step hc j)
  rw [← Finset.mul_sum] at h
  have ht : (∑ j ∈ Finset.range n, (1/(1+c*2^j)-1/(1+c*2^(j+1)))) =
      1/(1+c) - 1/(1+c*2^n) := by
    have hh := Finset.sum_range_sub (fun j => (1 : ℝ)/(1+c*2^j)) n
    rw [Finset.sum_sub_distrib] at hh ⊢
    simp only [pow_zero,mul_one] at hh
    linarith
  rw [ht] at h
  have hc0 : 0 ≤ 2/c := by positivity
  have hfirst : 1/(1+c) ≤ (1 : ℝ) := (div_le_one (by positivity)).mpr (by linarith)
  have hlast : (0 : ℝ) ≤ 1/(1+c*2^n) := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left (by linarith : 1/(1+c)-1/(1+c*2^n) ≤ 1) hc0).trans_eq (mul_one _))

lemma dyadic_decay_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ => (2 : ℝ)^j/(1+c*2^j)^2) :=
  summable_of_sum_range_le (fun _ => by positivity) (dyadic_decay_partial_sum hc)

lemma dyadic_decay_tsum {c : ℝ} (hc : 0 < c) :
    (∑' j : ℕ, (2 : ℝ)^j/(1+c*2^j)^2) ≤ 2/c := by
  exact (dyadic_decay_summable hc).tsum_le_of_sum_range_le (dyadic_decay_partial_sum hc)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- The squarefree weight equals the squared absolute value of the normalized
Gauss sum, for primary elements. -/
theorem gauss_mul_star_squarefree {a : Eisenstein} (ha : primary a) :
    gauss a * star (gauss a) = if Squarefree a then (1 : ℂ) else 0 := by
  have hnorm := Complex.mul_conj' (gauss a)
  simp only [starRingEnd_apply] at hnorm
  rw [hnorm, norm_gauss ha]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coefficient bounds for a bounded number of ordered prime factors. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every prime in another tuple with the same product occurs in the
reference tuple. This includes repeated primes. -/
lemma prime_tuple_range_subset (f g : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hg : ∀ i, primaryPrime (g i))
    (hprod : (∏ i, g i) = ∏ i, f i) (i : ι) :
    g i ∈ Finset.univ.image f := by
  have hd : g i ∣ ∏ j, f j := hprod ▸ Finset.dvd_prod_of_mem g (Finset.mem_univ i)
  obtain ⟨j,_,hj⟩ := ((hg i).2.dvd_finsetProd_iff f).mp hd
  have he : g i = f j := primary_associated_eq (hg i).1 (hf j).1
    (((hg i).2.dvd_prime_iff_associated (hf j).2).mp hj)
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩

/-- The deliberately generous `k^k` bound avoids ordering conventions and
is uniform in the norm and in all independent supports. -/
theorem prime_tuple_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (b : Eisenstein) :
    ((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card ≤
      (Fintype.card ι)^(Fintype.card ι) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  by_cases ht : T.Nonempty
  · obtain ⟨f,hf⟩ := ht
    have hfs := (Finset.mem_filter.mp hf).1
    have hfb := (Finset.mem_filter.mp hf).2
    have hprime : ∀ i, primaryPrime (f i) :=
      fun i => hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)
    have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.univ.image f) := by
      intro g hg
      obtain ⟨hgs,hgb⟩ := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      exact prime_tuple_range_subset f g hprime
        (fun i => hS i (g i) ((Fintype.mem_piFinset.mp hgs) i)) (hgb.trans hfb.symm)
    calc
      T.card ≤ (Fintype.piFinset (fun _ : ι => Finset.univ.image f)).card :=
        Finset.card_le_card hsub
      _ = ((Finset.univ.image f).card)^(Fintype.card ι) := by
        simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left (by
        simpa using (Finset.card_image_le (s := (Finset.univ:Finset ι)) (f := f))) _
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ _
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- The coefficient bound depends only on the number of prime factors
and on their separate weight bounds, including for nonsquarefree products. -/
theorem orderedConvolution_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  have hprod : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  unfold orderedConvolution
  calc
    _ ≤ ∑ f ∈ T, ‖∏ i, w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ T, ∏ i, M i := by
      apply Finset.sum_le_sum
      intro f hf
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => _root_.norm_nonneg _)
        (fun i _ => hw i (f i) ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1) i))
    _ = (T.card:ℝ)*(∏ i, M i) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (prime_tuple_fiber_card S hS b)) hprod

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the original independently weighted prime tuples,
with the individual support and the global norm cutoff both retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ n ∈ coordinateSupport W X Y i, primary n := by
  intro i n hn
  exact (mem_primaryElementBall.mp (Finset.mem_filter.mp hn).1).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting the indicator convolution to genuine primary primes,
followed by the exact squarefree discrepancy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i, primaryPrime p := by
  intro i p hp
  exact ⟨coordinateSupport_primary W X Y i p (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredSupportBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The output norm range is derived from the independent coordinate
supports; no product-range hypothesis is imposed on the coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_norm_bounds (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ}
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℝ) (i : ι) (p : Eisenstein) (hp : p ∈ coordinatePrimeSupport W X Z i) :
    X i ≤ norm p ∧ norm p ≤ R*X i := by
  have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  constructor
  · have h : 1 ≤ norm p/X i := le_of_not_gt (fun h => hn (hlo i _ h))
    simpa only [one_mul] using (le_div_iff₀ (hX i)).mp h
  · have h : norm p/X i ≤ R := le_of_not_gt (fun h => hn (hhi i _ h))
    exact (div_le_iff₀ (hX i)).mp h

lemma coordinatePrimeProduct_norm_bounds (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ} (_hR : 0 ≤ R)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℝ) (z : Eisenstein) (hz : z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z)) :
    (∏ i, X i) ≤ norm z ∧ norm z ≤ R^(Fintype.card ι)*(∏ i, X i) := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
  have hb (i : ι) := coordinatePrimeSupport_norm_bounds W X hX hlo hhi Z i (n i)
    (Fintype.mem_piFinset.mp hn i)
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod (fun i _ => (hX i).le) (fun i _ => (hb i).1)
  · calc
      _ ≤ ∏ i, R*X i := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hb i).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp

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

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_eq_coordinate {R Z : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hhi : ∀ i x, R < x → W i x = 0)
    (hZ : ∀ i, R*X i ≤ 2*Z) : fullPrimeSupport R W X = coordinatePrimeSupport W X Z := by
  funext i
  ext p
  rw [fullPrimeSupport_mem_iff W X hX hhi]
  simp only [coordinatePrimeSupport,coordinateSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨hp,hq⟩,hw⟩
    have hn : norm p/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
    exact ⟨⟨⟨hp,((div_le_iff₀ (hX i)).mp hn).trans (hZ i)⟩,hw⟩,hq⟩
  · rintro ⟨⟨⟨hp,_⟩,hw⟩,hq⟩
    exact ⟨⟨hp,hq⟩,hw⟩

lemma coordinate_le_product (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i) (i : ι) :
    X i ≤ ∏ j, X j := by
  rw [← Finset.mul_prod_erase _ X (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (by linarith [hX i]) (Finset.one_le_prod (fun j _ => hX j))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedScalePowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed dilations preserve every strict exponent margin used by the
finite output partition. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventually_const_mul_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ Y : ℝ in atTop, C*Y^a ≤ Y^b := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C] with Y hY hC
  calc
    _ ≤ Y^(b-a)*Y^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hY.le _)
    _ = _ := by rw [← Real.rpow_add hY]; congr 1; ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredCoefficientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coefficient energy needed by the noncube sieve follows from the
actual independent prime weights, including logarithmic weight families. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeMomentCoefficient_norm_le (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (Z : ℝ) (z : Eisenstein) :
    ‖primeMomentCoefficient W X Z z‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hz : Squarefree z
  · simpa only [primeMomentCoefficient,squarefreeConvolution,ite_eq_left hz] using
      orderedConvolution_norm_bound (coordinatePrimeSupport W X Z)
        (fun i n => W i (norm n/X i)) M (coordinatePrimeSupport_primary W X Z) hM
        (fun i p _ => hW i _) z
  · simpa only [primeMomentCoefficient,squarefreeConvolution,ite_eq_right hz,norm_zero] using
      mul_nonneg (Nat.cast_nonneg ((Fintype.card ι)^(Fintype.card ι)))
        (Finset.prod_nonneg (fun i _ => hM i))

lemma structuredCoefficient_energy_le (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (Z : ℝ) :
    (∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      ‖primeMomentCoefficient W X Z z‖^2) ≤
      18*(R^(Fintype.card ι)*(∏ i, X i))*
        (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  let S := orderedConvolutionSupport (coordinatePrimeSupport W X Z)
  have hcard : (S.card:ℝ) ≤ 18*(R^(Fintype.card ι)*(∏ i, X i)) :=
    primary_support_card_le S (mul_nonneg (pow_nonneg hR _)
      (Finset.prod_nonneg (fun i _ => (hX i).le))) (fun z hz =>
      ⟨orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
        (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) hz,
        (coordinatePrimeProduct_norm_bounds W X hX hR hlo hhi Z z hz).2⟩)
  calc
    _ ≤ ∑ _z ∈ S, (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 :=
      Finset.sum_le_sum (fun z _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
        (primeMomentCoefficient_norm_le W X M hM hW Z z) 2)
    _ = (S.card:ℝ)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

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

lemma fullPrimeSupport_eq_product_cutoff {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i)
    (hhi : ∀ i x, R < x → W i x = 0) :
    fullPrimeSupport R W X = coordinatePrimeSupport W X (R/2*(∏ i, X i)) := by
  apply fullPrimeSupport_eq_coordinate W X (fun i => zero_lt_one.trans_le (hX i)) hhi
  intro i
  have h := mul_le_mul_of_nonneg_left (coordinate_le_product X hX i) hR
  nlinarith

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicPrimeWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial derivative bounds of a logarithmic family, used to apply
the published prime Siegel–Walfisz input by actual partial summation. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma LogarithmicWeightFamily.norm_log_bound {γ : Type*}
    {L : γ → ℝ} {W : γ → ℝ → ℂ} (h : LogarithmicWeightFamily L W) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ i x, ‖W i x‖ ≤ C*(1+Real.log (L i))^A := by
  obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound 0
  refine ⟨C,A,hC,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he : Real.exp (-(-Real.log x)) = x := by simp [Real.exp_log hx]
    simpa only [norm_iteratedFDeriv_zero,he] using hbound i (-Real.log x)
  · have hz : W i x = 0 := by
      by_contra hn
      exact hx (h.positive i (subset_closure hn))
    rw [hz,norm_zero]
    exact mul_nonneg hC (pow_nonneg (by linarith [Real.log_nonneg (h.length_one i)]) _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogCoefficientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit logarithmic, rather than subpower, energy of the actual
full prime convolution. This is used in the small-conductor sieve range. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem logarithmic_full_coefficient_energy {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R (W r) X),
        ‖fullPrimeCoefficient R (W r) X z‖^2) ≤
        C*L r*(1+Real.log (L r))^A := by
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  let n := Fintype.card ι
  let C := 18*R^n*((n^n:ℕ)*M^n)^2
  refine ⟨C,2*m*n,?_,?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans hR) _)) (sq_nonneg _)
  intro r X hL hX hprod
  let Z := R/2*L r
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have heq : fullPrimeSupport R (W r) X = coordinatePrimeSupport (W r) X Z := by
    simpa only [Z,hprod] using fullPrimeSupport_eq_product_cutoff (zero_le_one.trans hR)
      (W r) X hX (hhi r)
  have hb := structuredCoefficient_energy_le (W r) X
    (fun _ => M*(1+Real.log (L r))^m) (fun i => zero_lt_one.trans_le (hX i))
    (zero_le_one.trans hR) (hlo r) (hhi r)
    (fun _ => mul_nonneg hM (pow_nonneg hz _)) (fun i x => hMb (r,i) x) Z
  have hcoeff : fullPrimeCoefficient R (W r) X = fun z => primeMomentCoefficient (W r) X Z z := by
    funext z
    unfold fullPrimeCoefficient primeMomentCoefficient
    rw [heq]
  rw [heq,hcoeff]
  apply hb.trans_eq
  rw [hprod,Finset.prod_const,Finset.card_univ,mul_pow,← pow_mul]
  dsimp only [C,n]
  rw [mul_pow,mul_pow,← pow_mul]
  have hm : m*(Fintype.card ι*2) = 2*m*Fintype.card ι := by ring
  rw [hm,pow_mul M (Fintype.card ι) 2]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeMellinEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial coarse envelope for the unchanged full prime rows,
uniform in Mellin height and the ambient set of prime divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeSupport_card_bound {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0) (e : Eisenstein) :
    ((fullSquarefreePrimeSupport R W X e).card:ℝ) ≤ 18*(R^Fintype.card ι*(∏ i, X i)) := by
  apply primary_support_card_le _ (mul_nonneg (pow_nonneg hR _) (Finset.prod_nonneg (fun i _ => (hX i).le)))
  intro b hb
  exact ⟨(fullSquarefreePrimeSupport_primary R W X e hb).1,
    (fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp hb).1).2⟩

lemma fullPrimeCoefficient_l1_square {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0) (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖)^2 ≤
      18*(R^Fintype.card ι*(∏ i, X i))*
        ∑ b ∈ orderedConvolutionSupport (fullPrimeSupport R W X), ‖fullPrimeCoefficient R W X b‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (fullSquarefreePrimeSupport R W X e)
    (fun _ => (1:ℝ)) (fun b => ‖fullPrimeCoefficient R W X b‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  apply hcs.trans
  apply mul_le_mul (fullPrimeSupport_card_bound hR W X hX hlo hhi e)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hR _) (Finset.prod_nonneg (fun i _ => (hX i).le))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal angular prime coefficients and the two signed Mellin rows.
Only unit phases are removed; the angular index remains fixed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

lemma angularHeightPrimeCoefficient_norm (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {b : Eisenstein} (hb : primary b) :
    ‖angularHeightPrimeCoefficient ℓ R W X b‖ = ‖fullPrimeCoefficient R W X b‖ := by
  rw [angularHeightPrimeCoefficient,norm_mul,norm_theta (primary_ne_zero hb),mul_one]

lemma angularHeightPrimeCoefficient_l1 (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖angularHeightPrimeCoefficient ℓ R W X b‖) =
    ∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖ := by
  exact Finset.sum_congr rfl (fun b hb => angularHeightPrimeCoefficient_norm ℓ R W X
    (fullSquarefreePrimeSupport_primary R W X e hb).1)

lemma angularHeightPrimeCoefficient_energy (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖angularHeightPrimeCoefficient ℓ R W X b‖^2) =
    ∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2 := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [angularHeightPrimeCoefficient_norm ℓ R W X
    (fullSquarefreePrimeSupport_primary R W X e hb).1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogPoissonEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial/logarithmic envelope for all high Poisson frequencies
of the unchanged full prime convolution. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem logarithmic_full_l1_square {R : ℝ} (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (E : ℝ) (a : ℕ), 0 ≤ E ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → ∀ e : Eisenstein,
      (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e, ‖fullPrimeCoefficient R (W r) X b‖)^2 ≤
        E*(L r)^2*(1+Real.log (L r))^a := by
  obtain ⟨C,a,hC,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  refine ⟨18*R^Fintype.card ι*C,a,by positivity,?_⟩
  intro r X hL hX hprod e
  have hl := fullPrimeCoefficient_l1_square (zero_le_one.trans hR) (W r) X
    (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) e
  rw [hprod] at hl
  apply hl.trans
  apply (mul_le_mul_of_nonneg_left (henergy r X hL hX hprod) (by positivity)).trans_eq
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusionSavingPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomially bounded exclusion remains negligible compared with
a rough prime coordinate, with every prescribed logarithmic saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma exclusion_log_absorption {c d ε : ℝ} (hε : 0 < ε) (hgap : d*ε < c)
    {C : ℝ} (hC : 0 ≤ C) (m k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Y E : ℝ, 0 ≤ E → E ≤ L^d → L^c ≤ Y →
      C*E^ε*(1+Real.log L)^m ≤ Y/(1+Real.log L)^k := by
  let s := (c-d*ε)/2
  have hs : 0 < s := by dsimp [s]; linarith
  have hexp : d*ε+s < c := by dsimp [s]; linarith
  obtain ⟨K,hK,hlog⟩ := log_power_normalization_bound (m+k) hs
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_const_mul_rpow_le hexp (C*K)]
    with L hL hbound
  intro Y E hE hEd hY
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL]
  have hlog' : (1+Real.log L)^(m+k) ≤ K*L^s := by
    calc
      _ = L^s*(L^(-s)*(1+Real.log L)^(m+k)) := by
        rw [← mul_assoc,← Real.rpow_add hLp]
        simp
      _ ≤ L^s*K := mul_le_mul_of_nonneg_left (hlog L hL) (Real.rpow_nonneg hLp.le _)
      _ = _ := mul_comm _ _
  apply (le_div_iff₀ (pow_pos hz k)).mpr
  calc
    _ = C*E^ε*(1+Real.log L)^(m+k) := by rw [pow_add]; ring
    _ ≤ C*(L^d)^ε*(K*L^s) := mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hE hEd hε.le) hC) hlog'
      (pow_nonneg hz.le _) (mul_nonneg hC (Real.rpow_nonneg (Real.rpow_nonneg hLp.le _) _))
    _ = (C*K)*L^(d*ε+s) := by
      rw [← Real.rpow_mul hLp.le,Real.rpow_add hLp]
      ring
    _ ≤ L^c := hbound
    _ ≤ Y := hY

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoreBlockMoment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One logarithmic saving on every actual core dyad above the small
core cutoff, obtained by joining the ordinary and exceptional estimates. -/
noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma negative_power_log_saving {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, L^(-ν) ≤ 1/(1+Real.log L)^k := by
  have h := exclusion_log_absorption (c := ν) (d := 0) (ε := 1)
    (by norm_num) (by simpa using hν) (C := 1) (by norm_num) k 0
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with L h hL
  have hp := h (L^ν) 1 (by norm_num) (by simp) le_rfl
  simp only [Real.one_rpow,one_mul,pow_zero,div_one] at hp
  have hz : 0 < (1+Real.log L)^k := pow_pos (by linarith [Real.log_nonneg hL]) _
  rw [Real.rpow_neg (zero_le_one.trans hL),← one_div]
  exact one_div_le_one_div_of_le hz hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeFrequencies
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact cube frequencies after square-divisor sieving

For a squarefree divisor `d`, the frequencies with `d*h` a cube are
precisely `d²*j³`. Every nonzero such frequency has three preimages.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Squarefreeness forces the full `d²` factor in a principal frequency. -/
theorem squarefree_mul_cube_iff {d h : Eisenstein} (hd : d ≠ 0) (hs : Squarefree d) :
    (∃ j : Eisenstein, d*h = j^3) ↔ ∃ j : Eisenstein, h = d^2*j^3 := by
  constructor
  · rintro ⟨j,hj⟩
    have hdj : d ∣ j := (hs.dvd_pow_iff_dvd (by norm_num : (3:ℕ) ≠ 0)).mp
      (hj ▸ dvd_mul_right d h)
    obtain ⟨k,rfl⟩ := hdj
    refine ⟨k,mul_left_cancel₀ hd ?_⟩
    calc
      d*h = (d*k)^3 := hj
      _ = d*(d^2*k^3) := by ring
  · rintro ⟨j,rfl⟩
    exact ⟨d*j,by ring⟩

lemma cube_eq_iff {x y : Eisenstein} :
    x^3 = y^3 ↔ x = y ∨ x = omegaE*y ∨ x = omegaE^2*y := by
  have hω : omegaE^2+omegaE+1 = 0 := Subtype.ext omega_quadratic
  have hfactor : x^3-y^3 = (x-y)*(x-omegaE*y)*(x-omegaE^2*y) := by
    linear_combination (x^2*y-x*y^2)*hω + (y^3-x*y^2)*(omegaE_cube)
  constructor
  · intro h
    have hz : (x-y)*(x-omegaE*y)*(x-omegaE^2*y) = 0 := by rw [← hfactor,h,sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  · rintro (rfl | rfl | rfl)
    · rfl
    · rw [mul_pow,omegaE_cube,one_mul]
    · rw [mul_pow,← pow_mul,show (2:ℕ)*3 = 3*2 by norm_num,pow_mul,omegaE_cube,one_pow,one_mul]

/-- The three roots differ exactly by the cube roots of unity. -/
theorem cube_fiber_eq {y : Eisenstein} :
    {x : Eisenstein | x^3 = y^3} = {y,omegaE*y,omegaE^2*y} := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_insert_iff,Set.mem_singleton_iff,cube_eq_iff]

/-- Every Eisenstein cube is a rational integer modulo three. -/
theorem cube_eq_integer_mod_three (j : Eisenstein) :
    ∃ n : ℤ, (3 : Eisenstein) ∣ j^3-(n : Eisenstein) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective j
  refine ⟨a^3+b^3-3*a*b^2,⟨((a*b*(a-b) : ℤ) : Eisenstein)*omegaE,?_⟩⟩
  have hω : omegaE^2+omegaE+1 = 0 := Subtype.ext omega_quadratic
  dsimp only [ofCoords]
  push_cast
  linear_combination (b : Eisenstein)^3*omegaE_cube +
    (3*(a : Eisenstein)*(b : Eisenstein)^2)*hω

lemma tracePhase_rational_mod_three {h : Eisenstein}
    (hh : ∃ n : ℤ, (3 : Eisenstein) ∣ h-(n : Eisenstein)) :
    (Real.fourierChar (tracePair (h : ℂ) (1/(3*traceLambda))) : ℂ) = 1 := by
  obtain ⟨n,k,hk⟩ := hh
  have he : (h : ℂ) = (n : ℂ)+3*(k : ℂ) := by
    have he' : h = (n : Eisenstein)+3*k := by linear_combination hk
    have hc := congrArg (eisensteinRing.val : Eisenstein → ℂ) he'
    simpa only [map_add,map_mul,map_ofNat,map_intCast,Subalgebra.val_apply] using hc
  have hz : tracePair (h : ℂ) (1/(3*traceLambda)) =
      tracePair (k : ℂ) (1/traceLambda) := by
    rw [he]
    have hpair : ((n : ℂ)+3*(k : ℂ))*(1/(3*traceLambda)) =
        (n : ℂ)/(3*traceLambda)+(k : ℂ)/traceLambda := by
      field_simp
    unfold tracePair
    rw [hpair,Complex.add_re]
    have hn : ((n : ℂ)/(3*traceLambda)).re = 0 := by
      rw [traceLambda_eq]
      simp [Complex.div_re,Complex.mul_re,Complex.mul_im]
    rw [hn,zero_add,div_eq_mul_inv,one_div]
  rw [hz,tracePhase_div_lambda_one]

/-- The additive phase in the Poisson formula is one on every principal
frequency produced by the squarefree majorant. -/
theorem squarefree_cube_frequency_phase {d : Eisenstein} (hd : primary d)
    (j : Eisenstein) :
    (Real.fourierChar (tracePair ((d^2*j^3 : Eisenstein) : ℂ)
      (1/(3*traceLambda))) : ℂ) = 1 := by
  obtain ⟨n,hn⟩ := cube_eq_integer_mod_three j
  apply tracePhase_rational_mod_three
  refine ⟨n,?_⟩
  have hd2 : (3 : Eisenstein) ∣ d^2-1 := by
    have h := primary_mul hd hd
    simpa only [primary,pow_two] using h
  have hs := dvd_add (dvd_mul_of_dvd_left hd2 (j^3)) hn
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma omegaE_mul_injective {y : Eisenstein} (hy : y ≠ 0) :
    Function.Injective (fun i : Fin 3 => omegaE^(i : ℕ)*y) := by
  intro i j hij
  apply Fin.ext
  exact omegaE_primitive.pow_inj i.isLt j.isLt (mul_right_cancel₀ hy hij)

/-- The factor `1/3` in the cube-lattice sum is the exact fiber size,
including all three units whose cubes are one. -/
theorem cube_fiber_card {y : Eisenstein} (hy : y ≠ 0) :
    {x : Eisenstein | x^3 = y^3}.ncard = 3 := by
  have he : {x : Eisenstein | x^3 = y^3} =
      Set.range (fun i : Fin 3 => omegaE^(i : ℕ)*y) := by
    ext x
    rw [Set.mem_ofPred_eq,cube_eq_iff,Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0,by simp⟩
      · exact ⟨1,by simp⟩
      · exact ⟨2,by simp⟩
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
  rw [he,Set.ncard_range_of_injective (omegaE_mul_injective hy)]
  simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The squarefree majorant in corrected dispersion

Only the positive variance term is majorized. The mixed and model terms
retain their actual Möbius-square weights.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Expansion before collecting pairs by their least common multiple. -/
theorem truncatedSquareDivisorSum_sq (C : Finset Eisenstein) (a : Eisenstein) :
    (truncatedSquareDivisorSum C a)^2 =
      ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c : ℝ)*(idealMoebius d : ℝ)*
        (if c^2 ∣ a ∧ d^2 ∣ a then (1 : ℝ) else 0) := by
  rw [truncatedSquareDivisorSum,pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc' : c^2 ∣ a <;> by_cases hd' : d^2 ∣ a <;> simp [hc',hd']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeJoin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collecting the squarefree majorant by least common multiples

The join is the product of the union of the primary prime factors. Its
square divides an element exactly when both input squares divide it.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma join_factor_primaryPrime {a b p : Eisenstein} (ha : primary a) (hb : primary b)
    (hp : p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b) : primaryPrime p := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (primaryPrimeFactor_spec ha hp).1
  · exact (primaryPrimeFactor_spec hb hp).1

lemma primarySquarefreeJoin_primary {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    primary (primarySquarefreeJoin a b) :=
  primary_finset_prod _ _ (fun _p hp => (join_factor_primaryPrime ha hb hp).1)

lemma primarySquarefreeJoin_squarefree {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    Squarefree (primarySquarefreeJoin a b) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact isRelPrime_iff_isCoprime.mpr
      (primaryPrimes_isCoprime (join_factor_primaryPrime ha hb hp)
        (join_factor_primaryPrime ha hb hq) hpq)
  · intro p hp
    exact (join_factor_primaryPrime ha hb hp).2.squarefree

lemma dvd_primarySquarefreeJoin_left {a b : Eisenstein} (ha : primary a) (hsa : Squarefree a) :
    a ∣ primarySquarefreeJoin a b := by
  nth_rw 1 [← primaryPrimeFactors_prod ha hsa]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left

lemma dvd_primarySquarefreeJoin_right {a b : Eisenstein} (hb : primary b) (hsb : Squarefree b) :
    b ∣ primarySquarefreeJoin a b := by
  nth_rw 1 [← primaryPrimeFactors_prod hb hsb]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_right

/-- This is the divisor condition used in the collected sieve square. -/
theorem primarySquarefreeJoin_sq_dvd_iff {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (n : Eisenstein) :
    (primarySquarefreeJoin a b)^2 ∣ n ↔ a^2 ∣ n ∧ b^2 ∣ n := by
  constructor
  · intro h
    exact ⟨(pow_dvd_pow_of_dvd (dvd_primarySquarefreeJoin_left ha hsa) 2).trans h,
      (pow_dvd_pow_of_dvd (dvd_primarySquarefreeJoin_right hb hsb) 2).trans h⟩
  · rintro ⟨han,hbn⟩
    unfold primarySquarefreeJoin
    rw [← Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact (primaryPrimes_isCoprime (join_factor_primaryPrime ha hb hp)
        (join_factor_primaryPrime ha hb hq) hpq).pow
    · intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (pow_dvd_pow_of_dvd (primaryPrimeFactor_spec ha hp).2 2).trans han
      · exact (pow_dvd_pow_of_dvd (primaryPrimeFactor_spec hb hp).2 2).trans hbn

lemma primarySquarefreeJoin_dvd_mul {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    primarySquarefreeJoin a b ∣ a*b := by
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    exact primaryPrimes_isCoprime (join_factor_primaryPrime ha hb hp)
      (join_factor_primaryPrime ha hb hq) hpq
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact dvd_mul_of_dvd_left (primaryPrimeFactor_spec ha hp).2 b
    · exact dvd_mul_of_dvd_right (primaryPrimeFactor_spec hb hp).2 a

lemma norm_le_of_dvd_nonzero {a b : Eisenstein} (hb : b ≠ 0) (h : a ∣ b) : norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := by intro h; apply hb; rw [h,mul_zero]
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_norm hc)

lemma primarySquarefreeJoin_norm_le {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    norm (primarySquarefreeJoin a b) ≤ norm a*norm b := by
  rw [← norm_mul_eq]
  exact norm_le_of_dvd_nonzero (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
    (primarySquarefreeJoin_dvd_mul ha hb)

private lemma weighted_image_sum {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (g : ι → κ) (v : ι → ℝ) (w : κ → ℝ) :
    (∑ t ∈ S, v t*w (g t)) =
      ∑ e ∈ S.image g, (∑ t ∈ S.filter (fun t => g t = e), v t)*w e := by
  have hf := Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g)
    (fun t ht => Finset.mem_image_of_mem g ht) (fun t => v t*w (g t))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(Finset.mem_filter.mp ht).2]

/-- The square of the truncated Möbius sum is exactly a finite divisor
sum with the collected coefficients. -/
theorem truncatedSquareDivisorSum_collected (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) (n : Eisenstein) :
    (truncatedSquareDivisorSum C n)^2 =
      ∑ e ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
        collectedSquarefreeSieveCoefficient C e * (if e^2 ∣ n then (1 : ℝ) else 0) := by
  rw [truncatedSquareDivisorSum_sq]
  calc
    _ = ∑ t ∈ C.product C, (idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ)*
        (if (primarySquarefreeJoin t.1 t.2)^2 ∣ n then (1 : ℝ) else 0) := by
      symm
      calc
        _ = ∑ a ∈ C, ∑ b ∈ C, (idealMoebius a : ℝ)*(idealMoebius b : ℝ)*
            (if (primarySquarefreeJoin a b)^2 ∣ n then (1 : ℝ) else 0) :=
          Finset.sum_product C C _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [primarySquarefreeJoin_sq_dvd_iff (hC a ha).1 (hC b hb).1 (hC a ha).2 (hC b hb).2]
          by_cases h : a^2 ∣ n ∧ b^2 ∣ n <;> simp [h]
    _ = _ := weighted_image_sum (C.product C)
      (fun t => primarySquarefreeJoin t.1 t.2)
      (fun t => (idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ))
      (fun e => if e^2 ∣ n then (1 : ℝ) else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveMobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Möbius coefficient below the sieve truncation

The union convolution of the squarefree Möbius weights is the same
Möbius weight. This proves the exact low-divisor coefficient identity,
which is stronger than a divisor bound and is needed in the residue.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_squarefreeDivisorTruncation {D : ℝ} {c : Eisenstein} :
    c ∈ squarefreeDivisorTruncation D ↔ primary c ∧ Squarefree c ∧ norm c ≤ D := by
  simp only [squarefreeDivisorTruncation,squareDivisorTruncation,Finset.mem_filter,
    mem_nonzeroNormBall]
  constructor
  · rintro ⟨⟨⟨hn,_⟩,hp⟩,hs⟩
    exact ⟨hp,hs,hn⟩
  · rintro ⟨hp,hs,hn⟩
    exact ⟨⟨⟨hn,primary_ne_zero hp⟩,hp⟩,hs⟩

end CubicFirstMoment

end

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Three-to-one summation of cube frequencies

This is the exact multiplicity correction before estimating the cube
lattice. Summability is stated explicitly so that regrouping is valid.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma cube_fiber_sum (F : Eisenstein → ℂ) (h : Eisenstein) :
    (∑' j : {j : Eisenstein // j^3 = h},
      if (j : Eisenstein) = 0 then 0 else F ((j : Eisenstein)^3)) =
      if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then 3*F h else 0 := by
  by_cases hh : h = 0
  · subst h
    rw [ite_eq_right (by simp)]
    have hz : (fun j : {j : Eisenstein // j^3 = 0} =>
        if (j : Eisenstein) = 0 then (0:ℂ) else F ((j : Eisenstein)^3)) = fun _ => 0 := by
      funext j
      have hj : (j : Eisenstein) = 0 := (pow_eq_zero_iff (by norm_num : (3:ℕ) ≠ 0)).mp j.property
      simp [hj]
    rw [hz,tsum_zero]
  · by_cases hex : ∃ j : Eisenstein, j^3 = h
    · obtain ⟨y,hy⟩ := hex
      have hy0 : y ≠ 0 := by intro hy0; apply hh; rw [← hy,hy0]; simp
      have hfinite : {j : Eisenstein | j^3 = h}.Finite := by
        rw [← hy,cube_fiber_eq]
        exact Set.toFinite _
      let : Fintype {j : Eisenstein // j^3 = h} := hfinite.fintype
      have hcard : Fintype.card {j : Eisenstein // j^3 = h} = 3 := by
        rw [← Nat.card_eq_fintype_card]
        change {j : Eisenstein | j^3 = h}.ncard = 3
        rw [← hy]
        exact cube_fiber_card hy0
      rw [ite_eq_left ⟨hh,⟨y,hy⟩⟩]
      calc
        _ = ∑ j : {j : Eisenstein // j^3 = h}, F h := by
          rw [tsum_fintype]
          apply Finset.sum_congr rfl
          intro j hj
          have hj0 : (j : Eisenstein) ≠ 0 := by
            intro hz
            apply hh
            rw [← j.property,hz]
            simp
          rw [ite_eq_right hj0,j.property]
        _ = 3*F h := by simp [hcard]
    · rw [ite_eq_right (by simp [hex])]
      let : IsEmpty {j : Eisenstein // j^3 = h} := ⟨fun j => hex ⟨j,j.property⟩⟩
      exact tsum_empty

/-- Regrouping the nonzero cubes divides their lattice parametrization
by exactly three. No asymptotic estimate enters this identity. -/
theorem tsum_nonzero_cubes (F : Eisenstein → ℂ)
    (hF : Summable (fun j : Eisenstein => if j = 0 then 0 else F (j^3))) :
    (∑' j : Eisenstein, if j = 0 then 0 else F (j^3)) =
      3*(∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then F h else 0) := by
  calc
    _ = ∑' h : Eisenstein, ∑' j : {j : Eisenstein // j^3 = h},
        if (j : Eisenstein) = 0 then 0 else F ((j : Eisenstein)^3) :=
      (hF.hasSum.tsum_fiberwise (fun j : Eisenstein => j^3)).tsum_eq.symm
    _ = ∑' h : Eisenstein,
        if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then 3*F h else 0 :=
      tsum_congr (cube_fiber_sum F)
    _ = _ := by
      calc
        _ = ∑' h : Eisenstein, 3*(if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then F h else 0) := by
          apply tsum_congr
          intro h
          split_ifs <;> simp
        _ = _ := tsum_mul_left

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The convergent cube lattice in dispersion

Rapid decay of the actual radial Fourier profile justifies the cube
regrouping. The factor one third is proved from the arithmetic fibers.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eisenstein_norm_pow_lattice (a : Eisenstein) (n : ℕ) : norm (a^n) = (norm a)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

/-- Decay of the Fourier profile makes the cube lattice absolutely
summable for every positive scale. -/
theorem summable_radial_cube_lattice (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {c : ℝ} (hc : 0 < c) :
    Summable (fun j : Eisenstein => radialDualProfile W (c*(norm j)^3)) := by
  obtain ⟨C,hC,hbound⟩ := radialDualProfile_rapidDecay W hW hW' 1
  apply ((summable_eisenstein_norm_rpow (s := 3) (by norm_num)).mul_left (C/c)).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : Eisenstein)] with j hj
  have hn := norm_pos_of_ne_zero hj
  have hp : 0 < c*(norm j)^3 := by positivity
  have hb := hbound (c*(norm j)^3) hp.le
  simp only [pow_one] at hb
  have hb' : ‖radialDualProfile W (c*(norm j)^3)‖*(c*(norm j)^3) ≤ C := by
    nlinarith [_root_.norm_nonneg (radialDualProfile W (c*(norm j)^3))]
  calc
    _ ≤ C/(c*(norm j)^3) := (le_div_iff₀ hp).mpr hb'
    _ = (C/c)*norm j^(-(3:ℝ)) := by
      rw [Real.rpow_neg hn.le,Real.rpow_ofNat]
      field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeSchwartz
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic pullback of the radial Fourier transform is a Schwartz function. -/

noncomputable section
open scoped SchwartzMap ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubeProfileSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (z : ℂ) :
    cubeProfileSchwartz W hW hW' z = radialDualProfile W ((Complex.normSq z)^3) := by
  change normProfileFourierSchwartz W hW hW' (z^3) = _
  rw [normProfileFourierSchwartz_apply,normProfileFourier_radial,map_pow]

lemma cubeProfileSchwartz_scaled_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (s : ℝ) (j : Eisenstein) :
    cubeProfileSchwartz W hW hW' ((s:ℂ)*(j:ℂ)) =
      radialDualProfile W ((s^2)^3*(norm j)^3) := by
  rw [cubeProfileSchwartz_apply,Complex.normSq_mul,Complex.normSq_ofReal,mul_pow]
  simp only [← pow_two]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SchwartzLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- Rapid decay gives a uniform bound for the nonzero dual lattice. -/
theorem schwartz_dual_lattice_tail (F : 𝓢(ℂ,ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w ≠ 0 →
      ‖∑' h : Eisenstein, if h = 0 then 0 else traceFourier F ((h:ℂ)/w)‖ ≤
        C*(Complex.normSq w)^2 := by
  obtain ⟨D,hD,hdecay⟩ := (traceFourierSchwartz F).decay 4 0
  simp only [norm_iteratedFDeriv_zero,traceFourierSchwartz_apply] at hdecay
  let R := ∑' h : Eisenstein, (norm h)^(-(2:ℝ))
  have hR : 0 ≤ R := tsum_nonneg (fun h => Real.rpow_nonneg (norm_nonneg h) _)
  refine ⟨D*R+1,by positivity,?_⟩
  intro w hw
  have hwN : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hs : Summable (fun h : Eisenstein => if h = 0 then (0:ℂ) else
      traceFourier F ((h:ℂ)/w)) := by
    apply (traceFourier_summable_eisenstein F w hw).norm.of_norm_bounded
    intro h
    by_cases hh : h = 0 <;> simp [hh]
  have hbound (h : Eisenstein) :
      ‖if h = 0 then (0:ℂ) else traceFourier F ((h:ℂ)/w)‖ ≤
        D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) := by
    by_cases hh : h = 0
    · simp only [ite_eq_left hh,norm_zero]
      exact mul_nonneg (mul_nonneg hD.le (sq_nonneg _))
        (Real.rpow_nonneg (norm_nonneg h) _)
    · rw [ite_eq_right hh]
      have hn : 0 < norm h := norm_pos_of_ne_zero hh
      have he : ‖(h:ℂ)/w‖^4 = (norm h)^2/(Complex.normSq w)^2 := by
        rw [show (4:ℕ) = 2*2 by norm_num,pow_mul,← Complex.normSq_eq_norm_sq,
          Complex.normSq_div,div_pow]
        rfl
      have hd := hdecay ((h:ℂ)/w)
      rw [he] at hd
      rw [Real.rpow_neg hn.le,Real.rpow_ofNat]
      apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
      apply (div_le_iff₀ (sq_pos_of_pos hwN)).mp
      convert hd using 1
      all_goals try with_reducible_and_instances rfl
      ring
  calc
    _ ≤ ∑' h : Eisenstein, ‖if h = 0 then (0:ℂ) else traceFourier F ((h:ℂ)/w)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' h : Eisenstein, D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) :=
      Summable.tsum_le_tsum hbound hs.norm
        ((summable_eisenstein_norm_rpow (s := 2) (by norm_num)).mul_left _)
    _ = D*R*(Complex.normSq w)^2 := by rw [tsum_mul_left]; dsimp [R]; ring
    _ ≤ (D*R+1)*(Complex.normSq w)^2 := by nlinarith [sq_nonneg (Complex.normSq w)]

lemma traceFourier_zero (F : ℂ → ℂ) : traceFourier F 0 = ∫ z : ℂ, F z := by
  simp [traceFourier,tracePair]

/-- The area-normalized lattice sum differs from its integral by O(s²).
This form is applied only to the fixed cubic Schwartz profile. -/
theorem schwartz_lattice_approximation (F : 𝓢(ℂ,ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s →
      ‖(∑' a : Eisenstein, F ((s:ℂ)*(a:ℂ))) -
        (2/(Real.sqrt 3*s^2):ℝ) • (∫ z : ℂ, F z)‖ ≤ C*s^2 := by
  obtain ⟨D,hD,hbound⟩ := schwartz_dual_lattice_tail F
  refine ⟨18*D/Real.sqrt 3,by positivity,?_⟩
  intro s hs
  have hsC : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hw : (s:ℂ)*traceLambda ≠ 0 := mul_ne_zero hsC traceLambda_ne_zero
  have hwN : Complex.normSq ((s:ℂ)*traceLambda) = 3*s^2 := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal,traceLambda_normSq]
    ring
  have hp := poisson_eisenstein_coset F (s:ℂ) hsC 0
  simp [tracePair,Complex.normSq_ofReal] at hp
  simp only [← pow_two] at hp
  have ht := (traceFourier_summable_eisenstein F _ hw).tsum_eq_add_tsum_ite 0
  simp only [Eisenstein.coe_zero,zero_div,traceFourier_zero] at ht
  have hp' : (∑' a : Eisenstein, F ((s:ℂ)*(a:ℂ))) =
      (2/(Real.sqrt 3*s^2):ℝ) •
        (∑' h : Eisenstein, traceFourier F ((h:ℂ)/((s:ℂ)*traceLambda))) := by
    simpa only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul,
      Complex.ofReal_ofNat,Complex.ofReal_pow] using hp
  rw [hp',ht,smul_add,add_sub_cancel_left]
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (hbound _ hw) (by positivity)).trans_eq
  rw [hwN]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeAsymptotic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral main term of the principal cube lattice. -/

noncomputable section
open scoped BigOperators SchwartzMap ContDiff
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubeProfileIntegral_eq (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    cubeProfileIntegral W = (2/Real.sqrt 3:ℝ) • ∫ z : ℂ, cubeProfileSchwartz W hW hW' z := by
  unfold cubeProfileIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  change normProfileFourier W (z^3) = normProfileFourierSchwartz W hW hW' (z^3)
  exact (normProfileFourierSchwartz_apply W hW hW' _).symm

/-- The nonzero cube lattice has its integral main term with a bounded
error for `q ≤ 1`. This is stronger than the radius-size error needed in
the low-height dispersion application. -/
theorem radial_cube_lattice_asymptotic (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q ≤ 1 →
      ‖(∑' j : Eisenstein, if j = 0 then (0:ℂ) else
          radialDualProfile W (q^3*(norm j)^3)) -
        (q⁻¹:ℝ) • cubeProfileIntegral W‖ ≤ C := by
  let F := cubeProfileSchwartz W hW hW'
  obtain ⟨D,hD,hbound⟩ := schwartz_lattice_approximation F
  refine ⟨D+‖F 0‖+1,by positivity,?_⟩
  intro q hq hq1
  let s := Real.sqrt q
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hs2 : s^2 = q := Real.sq_sqrt hq.le
  have hsC : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hh := hbound s hs
  rw [hs2] at hh
  have hF (j : Eisenstein) : F ((s:ℂ)*(j:ℂ)) =
      radialDualProfile W (q^3*(norm j)^3) := by
    dsimp only [F]
    rw [cubeProfileSchwartz_scaled_apply,hs2]
  have hsum := (schwartz_summable_eisenstein_coset F (s:ℂ) hsC 0).tsum_eq_add_tsum_ite 0
  simp only [zero_add,Eisenstein.coe_zero,mul_zero] at hsum
  have hmain : (2/(Real.sqrt 3*q):ℝ) • (∫ z : ℂ, F z) =
      (q⁻¹:ℝ) • cubeProfileIntegral W := by
    rw [cubeProfileIntegral_eq W hW hW',smul_smul]
    congr 1
    ring
  rw [hmain,hsum] at hh
  have hnonzero : (∑' j : Eisenstein, if j = 0 then (0:ℂ) else F ((s:ℂ)*(j:ℂ))) =
      ∑' j : Eisenstein, if j = 0 then 0 else radialDualProfile W (q^3*(norm j)^3) := by
    simp_rw [hF]
  rw [hnonzero] at hh
  let S := ∑' j : Eisenstein, if j = 0 then (0:ℂ) else radialDualProfile W (q^3*(norm j)^3)
  change ‖S-(q⁻¹:ℝ) • cubeProfileIntegral W‖ ≤ _
  calc
    _ = ‖(F 0+S-(q⁻¹:ℝ) • cubeProfileIntegral W)-F 0‖ := by congr 1; ring
    _ ≤ ‖F 0+S-(q⁻¹:ℝ) • cubeProfileIntegral W‖+‖F 0‖ := norm_sub_le _ _
    _ ≤ D*q+‖F 0‖ := add_le_add hh le_rfl
    _ ≤ D+‖F 0‖+1 := by nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubePoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual principal frequencies in the dispersion Poisson formula

At `h = d²*j³`, the additive phase is one and the character factors
are precisely the coprimality indicator. The radial argument loses its
`d` scale exactly, before any lattice estimate is applied.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicSymbol_cube_value {b : Eisenstein} (hb : primary b) (j : Eisenstein) :
    cubicSymbol b (j^3) = if IsCoprime b j then 1 else 0 := by
  rw [cubicSymbol_pow_upper hb]
  by_cases hj : IsCoprime b j
  · rw [ite_eq_left hj,cubicSymbol_cube_of_isCoprime hb j hj]
  · rw [ite_eq_right hj,cubicSymbol_eq_zero_of_not_isCoprime hb hj]
    simp

lemma cube_character_phase {b d : Eisenstein} (hb : primary b)
    (hbd : IsCoprime b d) (j : Eisenstein) :
    cubicSymbol b (d^2)*star (cubicSymbol b (d^2*j^3)) =
      if IsCoprime b j then 1 else 0 := by
  have hu : cubicSymbol b (d^2)*star (cubicSymbol b (d^2)) = 1 := by
    have hh := Complex.mul_conj' (cubicSymbol b (d^2))
    simpa only [starRingEnd_apply,norm_cubicSymbol_of_isCoprime hb hbd.pow_right,
      Complex.ofReal_one,one_pow] using hh
  rw [cubicSymbol_mul_upper hb,star_mul,cubicSymbol_cube_value hb]
  calc
    _ = (cubicSymbol b (d^2)*star (cubicSymbol b (d^2))) *
        star (if IsCoprime b j then (1:ℂ) else 0) := by ring
    _ = _ := by rw [hu,one_mul]; split_ifs <;> simp

lemma cube_mixed_character_phase {a b d : Eisenstein} (ha : primary a) (hb : primary b)
    (had : IsCoprime a d) (hbd : IsCoprime b d) (j : Eisenstein) :
    mixedSymbol b a (d^2)*
      (star (cubicSymbol b (d^2*j^3))*cubicSymbol a (d^2*j^3)) =
        if IsCoprime a j ∧ IsCoprime b j then 1 else 0 := by
  calc
    _ = (cubicSymbol b (d^2)*star (cubicSymbol b (d^2*j^3))) *
        star (cubicSymbol a (d^2)*star (cubicSymbol a (d^2*j^3))) := by
      simp only [mixedSymbol,star_mul,star_star]
      ring
    _ = _ := by
      rw [cube_character_phase hb hbd,cube_character_phase ha had]
      by_cases haj : IsCoprime a j <;> by_cases hbj : IsCoprime b j <;> simp [haj,hbj]

/-- This is the literal principal-frequency summand of the sieved
Poisson expansion. It retains the exclusion of common prime factors. -/
theorem cube_gramDualTerm {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hd : primary d)
    (had : IsCoprime a d) (hbd : IsCoprime b d)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) (j : Eisenstein) :
    mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) (d^2*j^3) =
      if IsCoprime a j ∧ IsCoprime b j then
        radialDualProfile W (A*(norm j)^3/(27*norm (b*a))) else 0 := by
  have hdn : norm d ≠ 0 := ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero hd))
  have hscale : 0 ≤ A/(norm d)^2 := div_nonneg hA (sq_nonneg _)
  rw [gramDualTerm_radial b a W hscale,squarefree_cube_frequency_phase hd,
    mul_one,← mul_assoc,cube_mixed_character_phase ha hb had hbd]
  have he : A/(norm d)^2*norm (d^2*j^3)/(27*norm (b*a)) =
      A*(norm j)^3/(27*norm (b*a)) := by
    rw [norm_mul_eq,eisenstein_norm_pow_lattice,eisenstein_norm_pow_lattice]
    field_simp
  rw [he]
  split_ifs <;> simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeLatticeBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The correctly scaled absolute cube-lattice bound

The dyadic norm count and rapid decay give the norm-area scale `q⁻¹`
for a profile evaluated at `q³ N(j)³`. This is the cube contribution
needed even when no lattice asymptotic is available.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma cube_decay_comparison {x : ℝ} (hx : 0 ≤ x) :
    (1+x)^2 ≤ 4*(1+x^3) := by
  have hs : x^2 ≤ 1+x^3 := by
    rcases le_total x 1 with h | h
    · have hsq : x^2 ≤ 1 := by nlinarith
      nlinarith [pow_nonneg hx 3]
    · have hp := mul_nonneg (sub_nonneg.mpr h) (sq_nonneg x)
      nlinarith
  nlinarith [sq_nonneg (x-1),pow_nonneg hx 3]

lemma radial_cube_pointwise_bound (W : ℝ → ℂ) {C q : ℝ}
    (hq : 0 < q)
    (hbound : ∀ t : ℝ, 0 ≤ t → (1+t)*‖radialDualProfile W t‖ ≤ C)
    (a : Eisenstein) :
    ‖radialDualProfile W (q^3*(norm a)^3)‖ ≤ 4*C/(1+q*norm a)^2 := by
  have hn := norm_nonneg a
  have hp := cube_decay_comparison (mul_nonneg hq.le (norm_nonneg a))
  have hb := hbound (q^3*(norm a)^3) (by positivity)
  have he : (q*norm a)^3 = q^3*(norm a)^3 := mul_pow _ _ _
  rw [he] at hp
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 1+q*norm a))).mpr
  have hmul := mul_le_mul_of_nonneg_right hp
    (_root_.norm_nonneg (radialDualProfile W (q^3*(norm a)^3)))
  nlinarith

/-- Uniform absolute bound at the cube-lattice scale. -/
theorem radial_cube_lattice_weighted_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 < q → ∀ w : Eisenstein → ℂ,
      (∀ j, ‖w j‖ ≤ 1) →
      ‖∑' j : Eisenstein, if j = 0 then (0:ℂ) else
        w j*radialDualProfile W (q^3*(norm j)^3)‖ ≤ K/q := by
  obtain ⟨C,hC,hbound'⟩ := radialDualProfile_rapidDecay W hW hW' 1
  have hbound : ∀ t : ℝ, 0 ≤ t → (1+t)*‖radialDualProfile W t‖ ≤ C := by
    simpa only [pow_one] using hbound'
  refine ⟨288*C,by positivity,?_⟩
  intro q hq w hw
  let F (j : Eisenstein) : ℂ := if j = 0 then 0 else w j*radialDualProfile W (q^3*(norm j)^3)
  have hF : Summable F := by
    apply (summable_radial_cube_lattice W hW hW' (pow_pos hq 3)).norm.of_norm_bounded
    intro j
    by_cases hj : j = 0
    · simp only [F,ite_eq_left hj,norm_zero]
      exact _root_.norm_nonneg _
    · simp only [F,ite_eq_right hj,norm_mul]
      exact mul_le_of_le_one_left (_root_.norm_nonneg _) (hw j)
  have hsum := hasSum_frequencyDyad F hF (by simp [F])
  have hrow (n : ℕ) : ‖∑ j ∈ frequencyDyad n, F j‖ ≤
      (144*C)*((2:ℝ)^n/(1+q*2^n)^2) := by
    have hden : 0 < (1+q*(2:ℝ)^n)^2 := by positivity
    calc
      _ ≤ ∑ j ∈ frequencyDyad n, ‖F j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ frequencyDyad n, 4*C/(1+q*(2:ℝ)^n)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        dsimp only [F]
        rw [ite_eq_right (mem_frequencyDyad.mp hj).1]
        rw [norm_mul]
        apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (hw j)).trans
        apply (radial_cube_pointwise_bound W hq hbound j).trans
        apply div_le_div_of_nonneg_left (by positivity) hden
        exact pow_le_pow_left₀ (by positivity)
          (by nlinarith [(frequencyDyad_norm hj).1]) 2
      _ = (frequencyDyad n).card*(4*C/(1+q*(2:ℝ)^n)^2) := by simp
      _ ≤ (36*(2:ℝ)^n)*(4*C/(1+q*(2:ℝ)^n)^2) :=
        mul_le_mul_of_nonneg_right (frequencyDyad_card_le n) (by positivity)
      _ = _ := by ring
  change ‖∑' j : Eisenstein, F j‖ ≤ _
  rw [← hsum.tsum_eq]
  calc
    _ ≤ ∑' n : ℕ, ‖∑ j ∈ frequencyDyad n, F j‖ := norm_tsum_le_tsum_norm hsum.summable.norm
    _ ≤ ∑' n : ℕ, (144*C)*((2:ℝ)^n/(1+q*2^n)^2) :=
      Summable.tsum_le_tsum hrow hsum.summable.norm ((dyadic_decay_summable hq).mul_left _)
    _ = (144*C)*(∑' n : ℕ, (2:ℝ)^n/(1+q*2^n)^2) := tsum_mul_left
    _ ≤ (144*C)*(2/q) := mul_le_mul_of_nonneg_left (dyadic_decay_tsum hq) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeExclusions
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cost of excluding prime divisors from the principal cube lattice. -/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The absolute sum has the same area bound as its arbitrary bounded twists. -/
theorem radial_cube_lattice_norm_sum_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 < q →
      (∑' j : Eisenstein, if j = 0 then 0 else
        ‖radialDualProfile W (q^3*(norm j)^3)‖) ≤ K/q := by
  obtain ⟨K,hK,hbound⟩ := radial_cube_lattice_weighted_bound W hW hW'
  refine ⟨K,hK,?_⟩
  intro q hq
  let f (j : Eisenstein) := radialDualProfile W (q^3*(norm j)^3)
  let w (j : Eisenstein) : ℂ := if f j = 0 then 0 else (‖f j‖ : ℂ)/f j
  have hw : ∀ j, ‖w j‖ ≤ 1 := by
    intro j
    by_cases hj : f j = 0
    · simp [w,hj]
    · simp [w,hj]
  have he (j : Eisenstein) : w j*f j = (‖f j‖ : ℂ) := by
    by_cases hj : f j = 0
    · simp [w,hj]
    · simp [w,hj]
  have hb := hbound q hq w hw
  simp_rw [show ∀ j, radialDualProfile W (q^3*(norm j)^3) = f j from fun _ => rfl,he] at hb
  have hc : (∑' j : Eisenstein, if j = 0 then (0:ℂ) else (‖f j‖ : ℂ)) =
      (((∑' j : Eisenstein, if j = 0 then (0:ℝ) else ‖f j‖) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro j
    split_ifs <;> simp
  rw [hc,Complex.norm_real,Real.norm_of_nonneg (tsum_nonneg (by intro j; split_ifs <;> positivity))] at hb
  exact hb

lemma tsum_divisible {R : Type*} [AddCommMonoid R] [TopologicalSpace R]
    (m : Eisenstein) (hm : m ≠ 0) (f : Eisenstein → R) :
    (∑' j : Eisenstein, if m ∣ j then f j else 0) = ∑' k : Eisenstein, f (m*k) := by
  let e : Eisenstein ≃ {j : Eisenstein // m ∣ j} :=
    Equiv.ofBijective (fun k => ⟨m*k,dvd_mul_right m k⟩)
      ⟨fun a b h => mul_left_cancel₀ hm (congrArg Subtype.val h),
        fun ⟨j,hj⟩ => by obtain ⟨k,rfl⟩ := hj; exact ⟨k,rfl⟩⟩
  change (∑' j : Eisenstein, Set.indicator {j | m ∣ j} f j) = _
  rw [← tsum_subtype]
  exact (e.tsum_eq (fun j => f j.val)).symm

/-- This remains valid when the sublattice spacing exceeds the natural
radius; there is no spurious constant term for the deleted origin. -/
theorem radial_cube_multiples_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 < q → ∀ m : Eisenstein, m ≠ 0 →
      (∑' j : Eisenstein, if m ∣ j ∧ j ≠ 0 then
        ‖radialDualProfile W (q^3*(norm j)^3)‖ else 0) ≤ K/(q*norm m) := by
  obtain ⟨K,hK,hbound⟩ := radial_cube_lattice_norm_sum_bound W hW hW'
  refine ⟨K,hK,?_⟩
  intro q hq m hm
  have he : (∑' j : Eisenstein, if m ∣ j ∧ j ≠ 0 then
      ‖radialDualProfile W (q^3*(norm j)^3)‖ else 0) =
      ∑' k : Eisenstein, if k = 0 then 0 else
        ‖radialDualProfile W ((q*norm m)^3*(norm k)^3)‖ := by
    calc
      _ = ∑' j : Eisenstein, if m ∣ j then
          (if j = 0 then 0 else ‖radialDualProfile W (q^3*(norm j)^3)‖) else 0 := by
        apply tsum_congr
        intro j
        by_cases hd : m ∣ j <;> by_cases hj : j = 0 <;> simp [hd,hj]
      _ = ∑' k : Eisenstein, if m*k = 0 then 0 else
          ‖radialDualProfile W (q^3*(norm (m*k))^3)‖ := tsum_divisible m hm _
      _ = _ := by
        apply tsum_congr
        intro k
        simp only [mul_eq_zero,hm,false_or,norm_mul_eq,mul_pow]
        congr 3
        ring
  rw [he]
  exact hbound (q*norm m) (mul_pos hq (norm_pos_of_ne_zero hm))

lemma not_coprime_prime_cover {a : Eisenstein} (ha : primary a) (hsa : Squarefree a)
    {j : Eisenstein} (hj : ¬IsCoprime a j) :
    ∃ p ∈ primaryPrimeFactors a, p ∣ j := by
  by_contra h
  apply hj
  have hall : ∀ p ∈ primaryPrimeFactors a, IsCoprime p j := by
    intro p hp
    exact (primaryPrimeFactor_spec ha hp).1.2.irreducible.coprime_iff_not_dvd.mpr
      (fun hd => h ⟨p,hp,hd⟩)
  have hh := IsCoprime.prod_left hall
  rwa [primaryPrimeFactors_prod ha hsa] at hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeRoughness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite prime-cover bound for restoring coprimality in the cube term. -/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_tsum_restriction_le_cover (f : Eisenstein → ℂ) (hf : Summable f)
    (P : Finset Eisenstein) (U : Eisenstein → Prop)
    (hcover : ∀ j, U j → ∃ p ∈ P, p ∣ j) :
    ‖∑' j : Eisenstein, if U j then f j else 0‖ ≤
      ∑ p ∈ P, ∑' j : Eisenstein, if p ∣ j then ‖f j‖ else 0 := by
  have hu : Summable (fun j => if U j then f j else 0) := by
    apply hf.norm.of_norm_bounded
    intro j
    split_ifs <;> simp
  have hp (p : Eisenstein) : Summable (fun j => if p ∣ j then ‖f j‖ else 0) := by
    apply hf.norm.of_nonneg_of_le
    · intro j; split_ifs <;> positivity
    · intro j; split_ifs <;> simp
  calc
    _ ≤ ∑' j : Eisenstein, ‖if U j then f j else 0‖ := norm_tsum_le_tsum_norm hu.norm
    _ ≤ ∑' j : Eisenstein, ∑ p ∈ P, if p ∣ j then ‖f j‖ else 0 := by
      apply Summable.tsum_le_tsum _ hu.norm (summable_sum (fun p _ => hp p))
      intro j
      by_cases hj : U j
      · obtain ⟨p,hp,hpj⟩ := hcover j hj
        simp only [ite_eq_left hj]
        exact (by simpa only [ite_eq_left hpj] using
          (Finset.single_le_sum (f := fun r => if r ∣ j then ‖f j‖ else 0)
            (fun r _ => by split_ifs <;> positivity) hp))
      · simp only [ite_eq_right hj,norm_zero]
        exact Finset.sum_nonneg (fun p _ => by split_ifs <;> positivity)
    _ = _ := Summable.tsum_finsetSum (fun p _ => hp p)

/-- Restoring coprimality costs exactly the expected sum of reciprocal
prime norms. The estimate is uniform over the lattice scale. -/
theorem radial_cube_coprimality_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 < q → ∀ a b : Eisenstein,
      primary a → Squarefree a → primary b → Squarefree b →
      ‖(∑' j : Eisenstein, if j = 0 then 0 else
          radialDualProfile W (q^3*(norm j)^3)) -
        (∑' j : Eisenstein, if j = 0 then 0 else
          (if IsCoprime a j ∧ IsCoprime b j then
            radialDualProfile W (q^3*(norm j)^3) else 0))‖ ≤
        K/q * ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p := by
  obtain ⟨K,hK,hbound⟩ := radial_cube_multiples_bound W hW hW'
  refine ⟨K,hK,?_⟩
  intro q hq a b ha hsa hb hsb
  let f (j : Eisenstein) : ℂ := if j = 0 then 0 else radialDualProfile W (q^3*(norm j)^3)
  let P := primaryPrimeFactors a ∪ primaryPrimeFactors b
  let U (j : Eisenstein) := ¬(IsCoprime a j ∧ IsCoprime b j)
  have hf : Summable f := by
    apply (summable_radial_cube_lattice W hW hW' (pow_pos hq 3)).norm.of_norm_bounded
    intro j
    by_cases hj : j = 0 <;> simp [f,hj]
  have hkeep : Summable (fun j => if U j then 0 else f j) := by
    apply hf.norm.of_norm_bounded
    intro j
    split_ifs <;> simp
  have hcover : ∀ j, U j → ∃ p ∈ P, p ∣ j := by
    intro j hj
    rcases not_and_or.mp hj with hj | hj
    · obtain ⟨p,hp,hd⟩ := not_coprime_prime_cover ha hsa hj
      exact ⟨p,Finset.mem_union_left _ hp,hd⟩
    · obtain ⟨p,hp,hd⟩ := not_coprime_prime_cover hb hsb hj
      exact ⟨p,Finset.mem_union_right _ hp,hd⟩
  have hdiff : (∑' j, f j) - (∑' j, if U j then 0 else f j) =
      ∑' j, if U j then f j else 0 := by
    rw [← hf.tsum_sub hkeep]
    apply tsum_congr
    intro j
    split_ifs <;> simp
  have hkeepEq (j : Eisenstein) : (if U j then 0 else f j) =
      if j = 0 then 0 else (if IsCoprime a j ∧ IsCoprime b j then
        radialDualProfile W (q^3*(norm j)^3) else 0) := by
    by_cases hj : j = 0 <;> by_cases hc : IsCoprime a j ∧ IsCoprime b j <;> simp [U,f,hj,hc]
  change ‖(∑' j, f j) - _‖ ≤ _
  simp_rw [← hkeepEq]
  rw [hdiff]
  calc
    _ ≤ ∑ p ∈ P, ∑' j : Eisenstein, if p ∣ j then ‖f j‖ else 0 := by
      convert norm_tsum_restriction_le_cover f hf P U hcover using 2
      all_goals try with_reducible_and_instances rfl
      apply tsum_congr
      intro j
      by_cases hj : U j <;> simp [hj]
    _ ≤ ∑ p ∈ P, K/(q*norm p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : p ≠ 0 := by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact (primaryPrimeFactor_spec ha hp).1.2.ne_zero
        · exact (primaryPrimeFactor_spec hb hp).1.2.ne_zero
      convert hbound q hq p hp0 using 1
      all_goals try with_reducible_and_instances rfl
      apply tsum_congr
      intro j
      by_cases hpj : p ∣ j <;> by_cases hj : j = 0 <;> simp [f,hpj,hj]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubePairAsymptotic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cube part of a Gram entry, with the multiplicity three
and the coprimality error retained. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramDualTerm_cube {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) (j : Eisenstein) :
    gramDualTerm b a W A (j^3) =
      if IsCoprime a j ∧ IsCoprime b j then
        radialDualProfile W (A*(norm j)^3/(27*norm (b*a))) else 0 := by
  have h := cube_gramDualTerm ha hb primary_one
    (isCoprime_one_right : IsCoprime a 1) (isCoprime_one_right : IsCoprime b 1) W hA j
  change mixedCubic b a (1^2)*gramDualTerm b a W (A/(norm 1)^2) (1^2*j^3) = _ at h
  simpa only [one_pow,one_mul,norm_one_eq,div_one,mixedCubic_one hb ha] using h

lemma cube_gram_series {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A q : ℝ} (hA : 0 ≤ A) (hq : 0 < q) (he : q^3 = A/(27*norm (b*a))) :
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
        gramDualTerm b a W A h else 0) =
      (1/3:ℂ)*(∑' j : Eisenstein, if j = 0 then 0 else
        (if IsCoprime a j ∧ IsCoprime b j then
          radialDualProfile W (q^3*(norm j)^3) else 0)) := by
  have hj (j : Eisenstein) : gramDualTerm b a W A (j^3) =
      if IsCoprime a j ∧ IsCoprime b j then
        radialDualProfile W (q^3*(norm j)^3) else 0 := by
    rw [gramDualTerm_cube ha hb W hA, he]
    congr 2
    ring
  have hs : Summable (fun j : Eisenstein => if j = 0 then (0:ℂ) else
      gramDualTerm b a W A (j^3)) := by
    apply (summable_radial_cube_lattice W hW hW' (pow_pos hq 3)).norm.of_norm_bounded
    intro j
    rw [hj]
    by_cases hz : j = 0
    · rw [ite_eq_left hz,norm_zero]
      positivity
    · rw [ite_eq_right hz]
      by_cases hc : IsCoprime a j ∧ IsCoprime b j
      · simp only [ite_eq_left hc,le_refl]
      · rw [ite_eq_right hc,norm_zero]
        positivity
  have h := tsum_nonzero_cubes (gramDualTerm b a W A) hs
  simp_rw [hj] at h
  linear_combination -(1/3:ℂ)*h

/-- A fixed radial weight has a uniform principal-frequency expansion.
The two errors are the bounded lattice error and the explicit rough-prime
exclusion error. The lattice scale is linked to the actual Poisson scale. -/
theorem cube_gram_asymptotic (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (a b : Eisenstein),
      primary a → Squarefree a → primary b → Squarefree b →
      ∀ A q : ℝ, 0 ≤ A → 0 < q → q ≤ 1 → q^3 = A/(27*norm (b*a)) →
      ‖(∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
          gramDualTerm b a W A h else 0) -
        (1/(3*q):ℝ) • cubeProfileIntegral W‖ ≤
        (C+K/q*∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p)/3 := by
  obtain ⟨C,hC,hmain⟩ := radial_cube_lattice_asymptotic W hW hW'
  obtain ⟨K,hK,hrough⟩ := radial_cube_coprimality_error W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro a b ha hsa hb hsb A q hA hq hq1 he
  let J := ∑' j : Eisenstein, if j = 0 then (0:ℂ) else
    radialDualProfile W (q^3*(norm j)^3)
  let Jc := ∑' j : Eisenstein, if j = 0 then (0:ℂ) else
    (if IsCoprime a j ∧ IsCoprime b j then
      radialDualProfile W (q^3*(norm j)^3) else 0)
  have hm : ‖J-(q⁻¹:ℝ) • cubeProfileIntegral W‖ ≤ C := hmain q hq hq1
  have hr : ‖J-Jc‖ ≤ K/q*∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p :=
    hrough q hq a b ha hsa hb hsb
  have hd : ‖Jc-(q⁻¹:ℝ) • cubeProfileIntegral W‖ ≤
      C+K/q*∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p := by
    calc
      _ = ‖(J-(q⁻¹:ℝ) • cubeProfileIntegral W)-(J-Jc)‖ := by congr 1; ring
      _ ≤ ‖J-(q⁻¹:ℝ) • cubeProfileIntegral W‖+‖J-Jc‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hm hr
  rw [cube_gram_series ha hb W hW hW' hA hq he]
  change ‖(1/3:ℂ)*Jc-(1/(3*q):ℝ) • cubeProfileIntegral W‖ ≤ _
  have heq : (1/3:ℂ)*Jc-(1/(3*q):ℝ) • cubeProfileIntegral W =
      (1/3:ℝ) • (Jc-(q⁻¹:ℝ) • cubeProfileIntegral W) := by
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul,
      Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_inv]
    ring
  rw [heq,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)]
  exact (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 1/3)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalContribution
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The absolute principal contribution to short dispersion

The actual cube-frequency kernel includes the Poisson scalar and the
three-to-one multiplicity. Its bound has size `A^(2/3) N(ab)^(-1/6)`.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma principal_cube_prefactor_scale {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    (A/(27*Real.sqrt R))/(A/(27*R))^(1/3:ℝ) =
      (1/9:ℝ)*A^(2/3:ℝ)*R^(-(1/6:ℝ)) := by
  have h27 : (27:ℝ)^(1/3:ℝ) = 3 := by
    rw [show (27:ℝ) = 3^3 by norm_num,← Real.rpow_natCast (3:ℝ) 3,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hAA : A/A^(1/3:ℝ) = A^(2/3:ℝ) := by
    nth_rw 1 [← Real.rpow_one A]
    rw [← Real.rpow_sub hA]
    norm_num
  have hRR : R^(1/3:ℝ)/R^(1/2:ℝ) = R^(-(1/6:ℝ)) := by
    rw [← Real.rpow_sub hR]
    norm_num
  rw [Real.div_rpow hA.le (by positivity : 0 ≤ 27*R),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 27) hR.le,h27,Real.sqrt_eq_rpow]
  calc
    _ = (1/9:ℝ)*(A/A^(1/3:ℝ))*(R^(1/3:ℝ)/R^(1/2:ℝ)) := by field_simp; ring
    _ = _ := by rw [hAA,hRR]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeScalar
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling of the cubic lattice main term in the Poisson formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cube_poisson_scale {A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    A/(9*Real.sqrt N)*(1/(3*(A/(27*N))^(1/3:ℝ))) =
      A^(2/3:ℝ)*N^(-(1/6:ℝ))/9 := by
  calc
    _ = (A/(27*Real.sqrt N))/(A/(27*N))^(1/3:ℝ) := by ring
    _ = _ := by rw [principal_cube_prefactor_scale hA hN]; ring

lemma cube_poisson_root {A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    ((A/(27*N))^(1/3:ℝ))^3 = A/(27*N) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : (0:ℝ) ≤ A/(27*N))]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cube main term is the squared model polynomial, with the exact
primary-coset density 1/9. This is a finite identity without asymptotics. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cube_model_pair_factor (a b : Eisenstein) :
    (norm (b*a))^(-(1/6:ℝ)) = (norm a)^(-(1/6:ℝ))*(norm b)^(-(1/6:ℝ)) := by
  rw [norm_mul_eq,Real.mul_rpow (norm_nonneg _) (norm_nonneg _),mul_comm]

theorem cube_model_quadratic (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (I : ℂ) (A : ℝ) :
    (∑ a ∈ S, ∑ b ∈ S,
      (β a*normTwist u a)*star (β b*normTwist u b)*
        (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*I) =
      (A^(2/3:ℝ)/9:ℝ)*I*((‖dispersionModel S β u‖^2:ℝ):ℂ) := by
  have hs (x : ℝ) : star (x:ℂ) = (x:ℂ) := by simp
  rw [dispersionModel,complex_sum_norm_sq_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [cube_model_pair_factor]
  simp only [star_mul,hs,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring_nf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubePairError
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cube-lattice asymptotic at the exact scale of each Poisson entry. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cube_poisson_pair_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (a b : Eisenstein),
      primary a → Squarefree a → primary b → Squarefree b →
      ∀ A : ℝ, 0 < A → A ≤ 27*norm (b*a) →
      ‖(A/(9*Real.sqrt (norm (b*a))):ℝ)*
          (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
            gramDualTerm b a W A h else 0) -
        (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W‖ ≤
        C*A/(27*Real.sqrt (norm (b*a))) +
        K*(A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9)*
          ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cube_gram_asymptotic W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro a b ha hsa hb hsb A hA hAN
  have hN : 0 < norm (b*a) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero hb) (primary_ne_zero ha))
  let q := (A/(27*norm (b*a)))^(1/3:ℝ)
  have hq : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hq1 : q ≤ 1 := Real.rpow_le_one (by positivity)
    ((div_le_one (by positivity)).mpr hAN) (by norm_num)
  have hq3 : q^3 = A/(27*norm (b*a)) := cube_poisson_root hA hN
  have hbnd := hbound a b ha hsa hb hsb A q hA.le hq hq1 hq3
  let P := A/(9*Real.sqrt (norm (b*a)))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hscale : P*(1/(3*q)) = A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9 :=
    cube_poisson_scale hA hN
  have hid : (P:ℂ)*(∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
      gramDualTerm b a W A h else 0) -
      (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W =
    (P:ℂ)*((∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
      gramDualTerm b a W A h else 0)-(1/(3*q):ℝ) • cubeProfileIntegral W) := by
    rw [mul_sub,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,hscale]
  change ‖(P:ℂ)*_ - _‖ ≤ _
  rw [hid,norm_mul,Complex.norm_real,Real.norm_of_nonneg hP]
  apply (mul_le_mul_of_nonneg_left hbnd hP).trans_eq
  calc
    P*((C+K/q*∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p)/3) =
        C*P/3 + K*(P*(1/(3*q)))*
          ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p := by ring
    _ = _ := by rw [hscale]; dsimp [P]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeFiniteError
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the literal principal-frequency error over the coprime Gram pairs. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubePoissonContribution_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (A : ℝ), 0 < A → (∀ a ∈ S, ∀ b ∈ S, A ≤ 27*norm (b*a)) →
      ∀ (β : Eisenstein → ℂ) (u : ℝ),
      ‖cubePoissonContribution S β u W A-coprimeCubeMainTerm S β u W A‖ ≤
        ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then ‖β a‖*‖β b‖*
          (C*A/(27*Real.sqrt (norm (b*a))) +
          K*(A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9)*
            ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p) else 0 := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cube_poisson_pair_error W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro S hS A hA hAN β u
  unfold cubePoissonContribution coprimeCubeMainTerm
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le S _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le S _).trans
  apply Finset.sum_le_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    have he : (β a*normTwist u a)*star (β b*normTwist u b)*
        (A/(9*Real.sqrt (norm (b*a))):ℝ)*
          (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then gramDualTerm b a W A h else 0) -
        (β a*normTwist u a)*star (β b*normTwist u b)*
          (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W =
      ((β a*normTwist u a)*star (β b*normTwist u b))*
        ((A/(9*Real.sqrt (norm (b*a))):ℝ)*
          (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then gramDualTerm b a W A h else 0) -
          (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W) := by ring
    rw [he,norm_mul]
    simp only [norm_mul,norm_star,norm_normTwist,mul_one]
    exact mul_le_mul_of_nonneg_left (hbound a b (hS a ha).1 (hS a ha).2
      (hS b hb).1 (hS b hb).2 A hA (hAN a ha b hb)) (by positivity)
  · simp only [ite_eq_right hab,sub_self,norm_zero,le_refl]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeUniformError
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform cube error on a norm annulus. The first term is the lattice
error; the second records the actual reciprocal-prime exclusion loss. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_pair_norm_bounds {L : ℝ} (hL : 0 < L) {a b : Eisenstein}
    (ha : L ≤ norm a) (hb : L ≤ norm b) :
    L ≤ Real.sqrt (norm (b*a)) ∧ (norm (b*a))^(-(1/6:ℝ)) ≤ L^(-(1/3:ℝ)) := by
  have hN : L^2 ≤ norm (b*a) := by
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul hb ha hL.le (hL.le.trans hb)
  constructor
  · have h := Real.sqrt_le_sqrt hN
    simpa only [Real.sqrt_sq hL.le] using h
  · apply (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hL) hN (by norm_num)).trans_eq
    rw [← Real.rpow_natCast L 2,← Real.rpow_mul hL.le]
    norm_num

theorem cubePoissonContribution_uniform_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (A L P : ℝ), 0 < A → 0 < L → 0 ≤ P → A ≤ 27*L^2 →
      (∀ a ∈ S, L ≤ norm a) →
      (∀ a ∈ S, ∀ b ∈ S,
        (∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p) ≤ P) →
      ∀ (β : Eisenstein → ℂ) (u : ℝ),
      ‖cubePoissonContribution S β u W A-coprimeCubeMainTerm S β u W A‖ ≤
        (C*A/(27*L)+K*A^(2/3:ℝ)*L^(-(1/3:ℝ))*P/9)*(∑ a ∈ S, ‖β a‖)^2 := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cubePoissonContribution_error W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro S hS A L P hA hL hP hAL hN hprime β u
  have hAN (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) (hb : b ∈ S) :
      A ≤ 27*norm (b*a) := by
    apply hAL.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul (hN b hb) (hN a ha) hL.le (hL.le.trans (hN b hb))
  let M := C*A/(27*L)+K*A^(2/3:ℝ)*L^(-(1/3:ℝ))*P/9
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hrow (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) (hb : b ∈ S) :
      C*A/(27*Real.sqrt (norm (b*a))) +
        K*(A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9)*
          ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p ≤ M := by
    obtain ⟨hs,hr⟩ := cube_pair_norm_bounds hL (hN a ha) (hN b hb)
    apply add_le_add
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    · calc
        _ ≤ K*(A^(2/3:ℝ)*L^(-(1/3:ℝ))/9)*P := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by positivity)) (by norm_num)) hK.le
          · exact hprime a ha b hb
          · exact Finset.sum_nonneg (fun p _ => one_div_nonneg.mpr (norm_nonneg p))
          · positivity
        _ = _ := by ring
  apply (hbound S hS A hA hAN β u).trans
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, ‖β a‖*‖β b‖*M := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      split_ifs
      · exact mul_le_mul_of_nonneg_left (hrow a ha b hb) (by positivity)
      · positivity
    _ = _ := by
      dsimp only [M]
      simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeErrorPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic cutoff in H=L²/A suppresses the bounded cube-lattice
error. This is the precise elementary scale comparison used below. -/
noncomputable section
namespace CubicFirstMoment

lemma cube_lattice_error_scale {A L z : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hz : 0 < z) (a k : ℕ) (hcut : A ≤ L^2/z^(3*(a+k))) :
    A*L*z^a ≤ A^(2/3:ℝ)*L^(5/3:ℝ)/z^k := by
  have hA3 : (A^(1/3:ℝ))^3 = A := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hA.le]
    norm_num
  have hL3 : (L^(2/3:ℝ))^3 = L^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
    norm_num
  have hpow : (z^(a+k))^3 = z^(3*(a+k)) := by rw [← pow_mul]; congr 1; omega
  have hsmall : A^(1/3:ℝ)*z^(a+k) ≤ L^(2/3:ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (3:ℕ) ≠ 0)).mp
    rw [mul_pow,hA3,hpow,hL3]
    exact (le_div_iff₀ (pow_pos hz _)).mp hcut
  have hAexp : A^(2/3:ℝ)*A^(1/3:ℝ) = A := by rw [← Real.rpow_add hA]; norm_num
  have hLexp : L*L^(2/3:ℝ) = L^(5/3:ℝ) := by
    nth_rw 1 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    norm_num
  apply (le_div_iff₀ (pow_pos hz k)).mpr
  calc
    A*L*z^a*z^k = (A^(2/3:ℝ)*L)*(A^(1/3:ℝ)*z^(a+k)) := by
      rw [pow_add]
      calc
        _ = A*(L*z^a*z^k) := by ring
        _ = (A^(2/3:ℝ)*A^(1/3:ℝ))*(L*z^a*z^k) := by rw [hAexp]
        _ = _ := by ring
    _ ≤ (A^(2/3:ℝ)*L)*L^(2/3:ℝ) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by rw [mul_assoc,hLexp]

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

lemma fullPrime_pair_reciprocal_sum_le {R D : ℝ} (hD : 0 < D)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) {a b : Eisenstein}
    (ha : a ∈ fullSquarefreePrimeSupport R W X e)
    (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
    (∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p) ≤
      2*(Fintype.card ι:ℝ)/D := by
  have hp (z : Eisenstein) (hz : z ∈ fullSquarefreePrimeSupport R W X e)
      (p : Eisenstein) (hmem : p ∈ primaryPrimeFactors z) : D < norm p := by
    have hprim := (fullSquarefreePrimeSupport_primary R W X e hz).1
    have hpp := (primaryPrimeFactor_spec hprim hmem).1
    obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R W X hpp
      (primaryPrimeFactor_spec hprim hmem).2 (Finset.mem_filter.mp hz).1
    have hw := ((fullPrimeSupport_mem_iff W X hX hhi i p).mp hi).2
    have hn : 1 ≤ norm p/X i := le_of_not_gt (fun h => hw (hlo i _ h))
    exact (hrough i).trans_le (by simpa using (le_div_iff₀ (hX i)).mp hn)
  have hc (z : Eisenstein) (hz : z ∈ fullSquarefreePrimeSupport R W X e) :
      (primaryPrimeFactors z).card ≤ Fintype.card ι :=
    primeProduct_primeFactors_card _ (fullPrimeSupport_prime R W X) (Finset.mem_filter.mp hz).1
  have hcard : ((primaryPrimeFactors a ∪ primaryPrimeFactors b).card:ℝ) ≤ 2*(Fintype.card ι:ℝ) := by
    have hn := (Finset.card_union_le (primaryPrimeFactors a) (primaryPrimeFactors b)).trans
      (Nat.add_le_add (hc a ha) (hc b hb))
    exact_mod_cast (show (primaryPrimeFactors a ∪ primaryPrimeFactors b).card ≤ 2*Fintype.card ι by omega)
  calc
    _ ≤ ∑ _p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/D := by
      apply Finset.sum_le_sum
      intro p hmem
      have hn : D ≤ norm p := by
        rcases Finset.mem_union.mp hmem with h | h
        · exact (hp a ha p h).le
        · exact (hp b hb p h).le
      exact one_div_le_one_div_of_le hD hn
    _ = ((primaryPrimeFactors a ∪ primaryPrimeFactors b).card:ℝ)/D := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right hcard hD.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCubeLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal cube term has its model with arbitrary logarithmic
saving once H=L²/A is a sufficiently large log-power. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_cube_poisson_log_saving {R c : ℝ} (hR : 1 ≤ R) (hc : 0 < c)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (e : Eisenstein) (u : ℝ), T₀ ≤ L r → 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → (∀ i, (L r)^c < X i) →
      0 < A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      ‖cubePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A-
        coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,D,hC,hD,hbound⟩ := cubePoissonContribution_uniform_error V hV hV'
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_l1_square hR hW hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp (negative_power_log_saving hc (a+k))
  let K := C*E/27+2*(Fintype.card ι:ℝ)*D*E/9+1
  refine ⟨3*(a+k),K,T₀,by dsimp [K]; positivity,?_⟩
  intro r X A e u hT₀ hL hX hprod hrough hA hcut
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz₁ : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hz : 0 < 1+Real.log (L r) := zero_lt_one.trans_le hz₁
  have hAL : A ≤ (L r)^2 := hcut.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hz₁))
  have hS : ∀ b ∈ fullSquarefreePrimeSupport R (W r) X e, primary b ∧ Squarefree b :=
    fun b hb => fullSquarefreePrimeSupport_primary R (W r) X e hb
  have hN : ∀ b ∈ fullSquarefreePrimeSupport R (W r) X e, L r ≤ norm b := by
    intro b hb
    have hn := (fullPrimeProduct_norm_bounds R (W r) X
      (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) (Finset.mem_filter.mp hb).1).1
    simpa only [hprod] using hn
  have hp (a b : Eisenstein)
      (ha : a ∈ fullSquarefreePrimeSupport R (W r) X e)
      (hb : b ∈ fullSquarefreePrimeSupport R (W r) X e) :=
    fullPrime_pair_reciprocal_sum_le (Real.rpow_pos_of_pos hLp c)
      (W r) X (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) hrough e ha hb
  have hb := hbound _ hS A (L r) (2*(Fintype.card ι:ℝ)/(L r)^c) hA hLp (by positivity)
    (hAL.trans (by nlinarith [sq_nonneg (L r)])) hN (fun a ha b hb => hp a b ha hb)
    (angularHeightPrimeCoefficient ℓ R (W r) X) u
  have he : (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      ‖angularHeightPrimeCoefficient ℓ R (W r) X b‖)^2 ≤
      E*(L r)^2*(1+Real.log (L r))^a := by
    rw [angularHeightPrimeCoefficient_l1]
    exact henergy r X hL hX hprod e
  have hlattice := cube_lattice_error_scale hA hLp hz a k hcut
  have hlog : (1+Real.log (L r))^a*(L r)^(-c) ≤ 1/(1+Real.log (L r))^k := by
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  have hpower : (L r)^(-(1/3:ℝ))*(L r)^2 = (L r)^(5/3:ℝ) := by
    rw [← Real.rpow_natCast (L r) 2,← Real.rpow_add hLp]
    norm_num
  have hfactor : (C*A/(27*L r)+D*A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*
      (2*(Fintype.card ι:ℝ)/(L r)^c)/9)*(E*(L r)^2*(1+Real.log (L r))^a) =
      (C*E/27)*(A*L r*(1+Real.log (L r))^a)+
      (2*(Fintype.card ι:ℝ)*D*E/9)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
        ((1+Real.log (L r))^a*(L r)^(-c)) := by
    rw [← hpower]
    simp only [Real.rpow_neg hLp.le]
    field_simp
  apply (hb.trans (mul_le_mul_of_nonneg_left he (by positivity))).trans
  rw [hfactor]
  calc
    _ ≤ (C*E/27)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k)+
        (2*(Fintype.card ι:ℝ)*D*E/9)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
          (1/(1+Real.log (L r))^k) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hlattice (by positivity))
        (mul_le_mul_of_nonneg_left hlog (by positivity))
    _ = (C*E/27+2*(Fintype.card ι:ℝ)*D*E/9)*
        (A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ K*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [K]
      linarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelOverlapCounting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting the shared-prime pairs discarded in the coprime cube model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisible_row_card_le (S : Finset Eisenstein) {Y : ℝ} (hY : 0 ≤ Y)
    (hS : ∀ b ∈ S, b ≠ 0 ∧ norm b ≤ Y) (d : Eisenstein) (hd : d ≠ 0) :
    ((S.filter (fun b => d ∣ b)).card:ℝ) ≤ 18*Y/norm d := by
  have hdN := norm_pos_of_ne_zero hd
  have hs : S.filter (fun b => d ∣ b) ⊆ (nonzeroNormBall (Y/norm d)).image (fun b => d*b) := by
    intro b hb
    obtain ⟨hb,hdiv⟩ := Finset.mem_filter.mp hb
    obtain ⟨k,rfl⟩ := hdiv
    have hk : k ≠ 0 := fun hk => (hS (d*k) hb).1 (by rw [hk,mul_zero])
    have hn : norm k ≤ Y/norm d := by
      apply (le_div_iff₀ hdN).mpr
      simpa only [norm_mul_eq,mul_comm] using (hS (d*k) hb).2
    exact Finset.mem_image.mpr ⟨k,mem_nonzeroNormBall.mpr ⟨hn,hk⟩,rfl⟩
  calc
    _ ≤ ((nonzeroNormBall (Y/norm d)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hs).trans Finset.card_image_le
    _ ≤ 18*(Y/norm d) := nonzeroNormBall_card_le (by positivity)
    _ = _ := by ring

lemma noncoprime_row_card_le (S : Finset Eisenstein) {Y D : ℝ}
    (hY : 0 ≤ Y) (hD : 0 < D) (hS : ∀ b ∈ S, b ≠ 0 ∧ norm b ≤ Y)
    {a : Eisenstein} (ha : primary a) (hsa : Squarefree a)
    (hrough : ∀ p ∈ primaryPrimeFactors a, D ≤ norm p) :
    ((S.filter (fun b => ¬IsCoprime a b)).card:ℝ) ≤
      (primaryPrimeFactors a).card*(18*Y/D) := by
  have hs : S.filter (fun b => ¬IsCoprime a b) ⊆
      (primaryPrimeFactors a).biUnion (fun p => S.filter (fun b => p ∣ b)) := by
    intro b hb
    obtain ⟨hb,hcop⟩ := Finset.mem_filter.mp hb
    obtain ⟨p,hp,hpb⟩ := not_coprime_prime_cover ha hsa hcop
    exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hb,hpb⟩⟩
  calc
    _ ≤ ∑ p ∈ primaryPrimeFactors a, ((S.filter (fun b => p ∣ b)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hs).trans (Finset.card_biUnion_le)
    _ ≤ ∑ _p ∈ primaryPrimeFactors a, 18*Y/D := by
      apply Finset.sum_le_sum
      intro p hp
      exact (divisible_row_card_le S hY hS p (primaryPrimeFactor_spec ha hp).1.2.ne_zero).trans
        (div_le_div_of_nonneg_left (by positivity) hD (hrough p hp))
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PairOverlapEnergy
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary symmetric pair bound used to remove shared-prime
pairs from the quadratic cube model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma symmetric_pair_energy_le {α : Type*} (S : Finset α) (R : α → α → Prop)
    (hsym : ∀ a ∈ S, ∀ b ∈ S, R a b ↔ R b a) (w : α → ℝ) (M : ℝ)
    (hM : ∀ a ∈ S, ((S.filter (R a)).card:ℝ) ≤ M) :
    (∑ a ∈ S, ∑ b ∈ S, if R a b then w a*w b else 0) ≤ M*∑ a ∈ S, (w a)^2 := by
  have hrow : (∑ a ∈ S, ∑ b ∈ S, if R a b then (w a)^2 else 0) ≤
      M*∑ a ∈ S, (w a)^2 := by
    have he (a : α) : (∑ b ∈ S, if R a b then (w a)^2 else 0) =
        ((S.filter (R a)).card:ℝ)*(w a)^2 := by
      rw [← Finset.sum_filter]
      simp
    simp_rw [he]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_right (hM a ha) (sq_nonneg _))
  have hcol : (∑ a ∈ S, ∑ b ∈ S, if R a b then (w b)^2 else 0) ≤
      M*∑ a ∈ S, (w a)^2 := by
    rw [Finset.sum_comm]
    convert hrow using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hsym b hb a ha]
  have htwice : 2*(∑ a ∈ S, ∑ b ∈ S, if R a b then w a*w b else 0) ≤
      (∑ a ∈ S, ∑ b ∈ S, if R a b then (w a)^2 else 0) +
      (∑ a ∈ S, ∑ b ∈ S, if R a b then (w b)^2 else 0) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    by_cases h : R a b
    · simp only [ite_eq_left h]
      nlinarith [sq_nonneg (w a-w b)]
    · simp only [ite_eq_right h,mul_zero,zero_add,le_refl]
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeOverlapEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A shared prime in two rough prime products saves its norm in the
quadratic coefficient mass. This uses actual quotient lattice counts. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_noncoprime_degree {R D L : ℝ} (hR : 1 ≤ R)
    (hD : 0 < D) (hL : 0 < L) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hprod : (∏ i, X i) = L)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) {a : Eisenstein}
    (ha : a ∈ fullSquarefreePrimeSupport R W X e) :
    (((fullSquarefreePrimeSupport R W X e).filter (fun b => ¬IsCoprime a b)).card:ℝ) ≤
      18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L/D := by
  have hp := fullSquarefreePrimeSupport_primary R W X e ha
  have hS (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
      b ≠ 0 ∧ norm b ≤ R^Fintype.card ι*L := by
    refine ⟨primary_ne_zero (fullSquarefreePrimeSupport_primary R W X e hb).1,?_⟩
    simpa only [hprod] using
      (fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp hb).1).2
  have hpn (p : Eisenstein) (hpa : p ∈ primaryPrimeFactors a) : D ≤ norm p := by
    obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R W X
      (primaryPrimeFactor_spec hp.1 hpa).1 (primaryPrimeFactor_spec hp.1 hpa).2
      (Finset.mem_filter.mp ha).1
    have hw := ((fullPrimeSupport_mem_iff W X hX hhi i p).mp hi).2
    have hr : 1 ≤ norm p/X i := le_of_not_gt (fun h => hw (hlo i _ h))
    exact (hrough i).le.trans (by simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hr)
  have hcard : ((primaryPrimeFactors a).card:ℝ) ≤ (Fintype.card ι:ℝ) := by
    exact_mod_cast primeProduct_primeFactors_card _ (fullPrimeSupport_prime R W X)
      (Finset.mem_filter.mp ha).1
  calc
    _ ≤ (primaryPrimeFactors a).card*(18*(R^Fintype.card ι*L)/D) :=
      noncoprime_row_card_le _ (by positivity) hD hS hp.1 hp.2 hpn
    _ ≤ (Fintype.card ι:ℝ)*(18*(R^Fintype.card ι*L)/D) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem fullPrime_overlap_energy {R D L : ℝ} (hR : 1 ≤ R)
    (hD : 0 < D) (hL : 0 < L) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hprod : (∏ i, X i) = L)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) :
    (∑ a ∈ fullSquarefreePrimeSupport R W X e, ∑ b ∈ fullSquarefreePrimeSupport R W X e,
      if ¬IsCoprime a b then ‖fullPrimeCoefficient R W X a‖*‖fullPrimeCoefficient R W X b‖ else 0) ≤
      (18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L/D)*
        ∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X a‖^2 := by
  convert (symmetric_pair_energy_le (fullSquarefreePrimeSupport R W X e)
    (fun a b => ¬IsCoprime a b) (fun _ _ _ _ => not_congr isCoprime_comm)
    (fun a => ‖fullPrimeCoefficient R W X a‖)
    (18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L/D)
    (fun _ ha => by
      convert fullPrime_noncoprime_degree hR hD hL W X hX hprod hlo hhi hrough e ha using 1
      congr 2
      ext b
      simp only [Finset.mem_filter])) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeModelOverlap
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The difference between the full model square and its coprime
pair sum is supported on shared-prime pairs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cube_model_coprimality_error (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 < L) (hS : ∀ a ∈ S, L ≤ norm a) :
    ‖cubeModelTerm S β u V A-coprimeCubeMainTerm S β u V A‖ ≤
      (A^(2/3:ℝ)*L^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖)*
        (∑ a ∈ S, ∑ b ∈ S, if ¬IsCoprime a b then ‖β a‖*‖β b‖ else 0) := by
  let K := A^(2/3:ℝ)*L^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  unfold cubeModelTerm
  rw [← cube_model_quadratic S β u (cubeProfileIntegral V) A]
  unfold coprimeCubeMainTerm
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le S _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le S _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,ite_eq_right (not_not_intro hab),sub_self,norm_zero,mul_zero,le_refl]
  · simp only [ite_eq_right hab,ite_eq_left hab,sub_zero]
    have hN0 : 0 ≤ (norm (b*a))^(-(1/6:ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    rw [norm_mul,norm_mul,norm_mul,norm_star,norm_mul,norm_mul,norm_normTwist,
      norm_normTwist,mul_one,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9 by positivity)]
    have hn := (cube_pair_norm_bounds hL (hS a ha) (hS b hb)).2
    calc
      _ ≤ ‖β a‖*‖β b‖*(A^(2/3:ℝ)*L^(-(1/3:ℝ))/9)*‖cubeProfileIntegral V‖ := by
        gcongr
      _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCubeModelLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring all pairs in the cube model costs an arbitrary logarithmic
power on the actual rough prime convolution. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_cube_model_overlap_log_saving {R c : ℝ} (hR : 1 ≤ R) (hc : 0 < c)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u : ℝ),
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (∀ i, (L r)^c < X i) → 0 ≤ A →
      ‖cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp (negative_power_log_saving hc (a+k))
  let C := 2*R^Fintype.card ι*(Fintype.card ι:ℝ)*E*‖cubeProfileIntegral V‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,T₀,by positivity,?_⟩
  intro r X A e u hT₀ hL hX hprod hrough hA
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hN (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R (W r) X e) : L r ≤ norm b := by
    simpa only [hprod] using
      (fullPrimeProduct_norm_bounds R (W r) X (fun i => zero_lt_one.trans_le (hX i))
        (hlo r) (hhi r) (Finset.mem_filter.mp hb).1).1
  have hb := cube_model_coprimality_error _ (angularHeightPrimeCoefficient ℓ R (W r) X) u V hA hLp hN
  have ho := fullPrime_overlap_energy hR (Real.rpow_pos_of_pos hLp c) hLp (W r) X
    (fun i => zero_lt_one.trans_le (hX i)) hprod (hlo r) (hhi r) hrough e
  have hnorm (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R (W r) X e) :=
    angularHeightPrimeCoefficient_norm ℓ R (W r) X
      (fullSquarefreePrimeSupport_primary R (W r) X e hb).1
  have ho' : (∑ a ∈ fullSquarefreePrimeSupport R (W r) X e,
      ∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
        if ¬IsCoprime a b then ‖angularHeightPrimeCoefficient ℓ R (W r) X a‖*
          ‖angularHeightPrimeCoefficient ℓ R (W r) X b‖ else 0) ≤
      (18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L r/(L r)^c)*
        ∑ b ∈ fullSquarefreePrimeSupport R (W r) X e, ‖fullPrimeCoefficient R (W r) X b‖^2 := by
    convert ho using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hnorm a ha, hnorm b hb]
  have he : (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      ‖fullPrimeCoefficient R (W r) X b‖^2) ≤ E*L r*(1+Real.log (L r))^a :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)).trans
      (henergy r X hL hX hprod)
  have hlog : (1+Real.log (L r))^a*(L r)^(-c) ≤ 1/(1+Real.log (L r))^k := by
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  have hpower : (L r)^(-(1/3:ℝ))*(L r)^2 = (L r)^(5/3:ℝ) := by
    rw [← Real.rpow_natCast (L r) 2,← Real.rpow_add hLp]
    norm_num
  have hfactor :
      (A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖)*
        ((18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L r/(L r)^c)*
          (E*L r*(1+Real.log (L r))^a)) =
      C*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*((1+Real.log (L r))^a*(L r)^(-c)) := by
    rw [← hpower]
    simp only [Real.rpow_neg hLp.le]
    dsimp [C]
    field_simp
    ring
  apply (hb.trans (mul_le_mul_of_nonneg_left
    (ho'.trans (mul_le_mul_of_nonneg_left he (by positivity))) (by positivity))).trans
  rw [hfactor]
  calc
    _ ≤ C*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*(1/(1+Real.log (L r))^k) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ (C+1)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-divisor character can be absorbed into the original
coefficient. Its norm never increases, including at noncoprime inputs. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem finiteDivisorPoissonContribution_twist (d : Eisenstein)
    (S H : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    finiteDivisorPoissonContribution d S H β u W A =
      finitePoissonContribution S H (divisorTwistedCoefficient d β) u W (A/(norm d)^2) := by
  unfold finiteDivisorPoissonContribution finitePoissonContribution
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,divisorTwistedCoefficient,star_mul,star_star,mixedSymbol]
    ring
  · simp only [ite_eq_right hab]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorFrequencyDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dyads used by the divisor Poisson sum are dyads of d*h.
They form an exact finite-fiber partition, with no lost multiplicity. -/
noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem hasSum_divisorFrequencyDyad (d : Eisenstein) (hd : d ≠ 0)
    (F : Eisenstein → ℂ) (hF : Summable F) (h0 : F 0 = 0) :
    HasSum (fun j : ℕ => ∑ h ∈ divisorFrequencyDyad d hd j, F h) (∑' h : Eisenstein, F h) := by
  have he := hF.hasSum.tsum_fiberwise (fun h : Eisenstein => Nat.log 2 (normNat (d*h)))
  have hf (j : ℕ) : (∑' h : ((fun h : Eisenstein => Nat.log 2 (normNat (d*h))) ⁻¹' {j}), F h) =
      ∑ h ∈ divisorFrequencyDyad d hd j, F h := by
    rw [tsum_subtype]
    calc
      _ = ∑ h ∈ divisorFrequencyDyad d hd j,
          Set.indicator ((fun h : Eisenstein => Nat.log 2 (normNat (d*h))) ⁻¹' {j}) F h := by
        apply tsum_eq_sum
        intro h hh
        by_cases hz : h = 0
        · subst h
          simp [h0]
        · have hj : Nat.log 2 (normNat (d*h)) ≠ j := fun hj =>
            hh (mem_divisorFrequencyDyad.mpr (mem_frequencyDyad.mpr ⟨mul_ne_zero hd hz,hj⟩))
          exact Set.indicator_of_notMem (show h ∉
            ((fun h : Eisenstein => Nat.log 2 (normNat (d*h))) ⁻¹' {j}) from hj) F
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h hh
        exact Set.indicator_of_mem
          (show h ∈ ((fun h : Eisenstein => Nat.log 2 (normNat (d*h))) ⁻¹' {j}) from
            (mem_frequencyDyad.mp (mem_divisorFrequencyDyad.mp hh)).2) F
  simpa only [hf] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SievedDispersion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- Exact finite assembly: no error term is introduced when the
squarefree positive majorant is collected by its square divisor. -/
theorem sievedDispersionVariance_eq (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c)
    (B : Finset Eisenstein) (hB : ∀ b ∈ B, primary b)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    sievedDispersionVariance C B β u W A =
      ∑ d ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
        (collectedSquarefreeSieveCoefficient C d : ℂ)*
          divisorDispersionVariance d B β u W A := by
  let E := (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2)
  let H (d a : Eisenstein) : ℂ :=
    (collectedSquarefreeSieveCoefficient C d : ℂ) *
      (if primary a ∧ d^2 ∣ a then
        W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0)
  have hs (d : Eisenstein) : Summable (H d) :=
    (summable_restricted_dispersion (fun a => d^2 ∣ a) B hB β u W hW hW' hA).mul_left _
  have hp (a : Eisenstein) :
      (if primary a then (((truncatedSquareDivisorSum C a)^2 : ℝ) : ℂ)*
        W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0) =
        ∑ d ∈ E, H d a := by
    by_cases ha : primary a
    · rw [ite_eq_left ha]
      have hc := congrArg (fun x : ℝ => (x : ℂ)) (truncatedSquareDivisorSum_collected C hC a)
      push_cast at hc
      rw [Complex.ofReal_pow,hc,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp only [H]
      by_cases hd' : d^2 ∣ a <;> simp [ha,hd',mul_assoc]
    · simp [ha,H]
  unfold sievedDispersionVariance
  simp_rw [hp]
  rw [Summable.tsum_finsetSum (fun d _ => hs d)]
  apply Finset.sum_congr rfl
  intro d hd
  exact tsum_mul_left

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCubeSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact principal-frequency reindexing for the square-divisor sieve.
The factor d² disappears from the kernel before taking an asymptotic. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tsum_scaled_cubes (m : Eisenstein) (hm : m ≠ 0) (F : Eisenstein → ℂ) :
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, h = m*j^3) then F h else 0) =
      ∑' k : Eisenstein, if k ≠ 0 ∧ (∃ j : Eisenstein, j^3 = k) then F (m*k) else 0 := by
  let G := fun h : Eisenstein => if h ≠ 0 ∧ (∃ j : Eisenstein, h = m*j^3) then F h else 0
  have hG : (∑' h : Eisenstein, G h) = ∑' h : Eisenstein, if m ∣ h then G h else 0 := by
    apply tsum_congr
    intro h
    by_cases hh : h ≠ 0 ∧ (∃ j : Eisenstein, h = m*j^3)
    · obtain ⟨j,hj⟩ := hh.2
      rw [ite_eq_left (show m ∣ h from ⟨j^3,hj⟩)]
    · simp only [G,ite_eq_right hh,ite_self]
  rw [show (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, h = m*j^3) then F h else 0) =
    ∑' h : Eisenstein, G h from rfl,hG,tsum_divisible m hm]
  apply tsum_congr
  intro k
  have he : (∃ j : Eisenstein, m*k = m*j^3) ↔ ∃ j : Eisenstein, j^3 = k := by
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨j,(mul_left_cancel₀ hm hj).symm⟩
    · rintro ⟨j,rfl⟩
      exact ⟨j,rfl⟩
  have hn : m*k ≠ 0 ↔ k ≠ 0 := by
    constructor
    · intro h hk
      exact h (by rw [hk,mul_zero])
    · exact mul_ne_zero hm
  simp only [G,hn,he]

theorem divisor_cube_series {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hd : primary d)
    (had : IsCoprime a d) (hbd : IsCoprime b d)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, h = d^2*j^3) then
      mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h else 0) =
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
      gramDualTerm b a W A h else 0) := by
  rw [tsum_scaled_cubes (d^2) (pow_ne_zero _ (primary_ne_zero hd))]
  apply tsum_congr
  intro k
  by_cases hk : k ≠ 0 ∧ (∃ j : Eisenstein, j^3 = k)
  · rw [ite_eq_left hk,ite_eq_left hk]
    obtain ⟨j,rfl⟩ := hk.2
    rw [cube_gramDualTerm ha hb hd had hbd W hA,gramDualTerm_cube ha hb W hA]
  · rw [ite_eq_right hk,ite_eq_right hk]

theorem divisor_cube_series_effective {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hd : primary d) (hs : Squarefree d)
    (had : IsCoprime a d) (hbd : IsCoprime b d)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h) then
      mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h else 0) =
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
      gramDualTerm b a W A h else 0) := by
  have he (h : Eisenstein) : (∃ j : Eisenstein, j^3 = d*h) ↔
      ∃ j : Eisenstein, h = d^2*j^3 := by
    simpa only [eq_comm] using (squarefree_mul_cube_iff (h := h) (primary_ne_zero hd) hs)
  simp_rw [he]
  exact divisor_cube_series ha hb hd had hbd W hA

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCubeTerm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual principal part of a square-divisor Poisson block, with
the square-divisor density kept explicitly. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem divisorCubePoissonContribution_eq {d : Eisenstein} (hd : primary d)
    (hs : Squarefree d) (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ IsCoprime a d)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    divisorCubePoissonContribution d S β u W A =
      (1/(norm d)^2:ℝ)*cubePoissonContribution S β u W A := by
  unfold divisorCubePoissonContribution cubePoissonContribution
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    rw [divisor_cube_series_effective (hS a ha).1 (hS b hb).1 hd hs
      (hS a ha).2 (hS b hb).2 W hA]
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_one]
    ring
  · simp only [ite_eq_right hab,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorNoncubeIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The estimated divisor dyads are exactly the noncube part of the
full lattice Poisson sum, with the cube test at d*h. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma summable_finiteDivisorPoisson_singleton {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    Summable (fun h : Eisenstein => finiteDivisorPoissonContribution d S {h} β u V A) := by
  simp only [finiteDivisorPoissonContribution,Finset.sum_singleton]
  apply summable_sum
  intro a ha
  apply summable_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    have hdN := norm_pos_of_ne_zero hd
    have hs := (summable_gramDualTerm (hS b hb) (hS a ha) V hV hV'
      (show 0 < A/(norm d)^2 by positivity)).mul_left
        ((β a*normTwist u a)*star (β b*normTwist u b)*
          ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*mixedSymbol b a (d^2))
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    funext h
    ring
  · simp only [ite_eq_right hab]
    exact summable_zero

lemma tsum_divisor_noncube_dyads (d : Eisenstein) (hd : d ≠ 0)
    (F : Eisenstein → ℂ) (hF : Summable F) :
    (∑' j : ℕ, ∑ h ∈ (divisorFrequencyDyad d hd j).filter
        (fun h => ¬∃ z : Eisenstein, z^3 = d*h), F h) =
      ∑' h : Eisenstein, if ∃ z : Eisenstein, z^3 = d*h then 0 else F h := by
  let G := fun h : Eisenstein => if ∃ z : Eisenstein, z^3 = d*h then 0 else F h
  have he (h : Eisenstein) : G h = {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h}.indicator F h := by
    by_cases hh : ∃ z : Eisenstein, z^3 = d*h
    · simp only [G,ite_eq_left hh,Set.indicator_of_notMem (show h ∉
        {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h} from fun hn => hn hh)]
    · simp only [G,ite_eq_right hh,Set.indicator_of_mem (show h ∈
        {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h} from hh)]
  have hG : Summable G := by
    rw [show G = {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h}.indicator F from funext he]
    exact hF.indicator {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = d*h}
  have h0 : G 0 = 0 := by
    apply ite_eq_left
    exact ⟨0,by simp⟩
  have hblocks := hasSum_divisorFrequencyDyad d hd G hG h0
  have hblock (j : ℕ) : (∑ h ∈ divisorFrequencyDyad d hd j, G h) =
      ∑ h ∈ (divisorFrequencyDyad d hd j).filter
        (fun h => ¬∃ z : Eisenstein, z^3 = d*h), F h := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : ∃ z : Eisenstein, z^3 = d*h
    · simp only [G,ite_eq_left hh,ite_eq_right (not_not_intro hh)]
    · simp only [G,ite_eq_right hh,ite_eq_left hh]
  simp_rw [hblock] at hblocks
  exact hblocks.tsum_eq

theorem divisorNoncubePoissonContribution_lattice {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    divisorNoncubePoissonContribution d hd S β u V A =
      ∑' h : Eisenstein, if ∃ z : Eisenstein, z^3 = d*h then 0 else
        finiteDivisorPoissonContribution d S {h} β u V A := by
  let F := fun h : Eisenstein => finiteDivisorPoissonContribution d S {h} β u V A
  have he (H : Finset Eisenstein) : finiteDivisorPoissonContribution d S H β u V A =
      ∑ h ∈ H, F h := by
    simp only [F,finiteDivisorPoissonContribution,Finset.sum_singleton]
  calc
    _ = ∑' j : ℕ, ∑ h ∈ (divisorFrequencyDyad d hd j).filter
        (fun h => ¬∃ z : Eisenstein, z^3 = d*h), F h := by
      apply tsum_congr
      exact fun j => he _
    _ = _ := tsum_divisor_noncube_dyads d hd F
      (summable_finiteDivisorPoisson_singleton hd S hS β u V hV hV' hA)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCoprimePoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coprime component of the square-divisor variance, with its
literal lattice Poisson formula and its vanishing zero frequency. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem coprimeDispersionGram_poisson_lattice (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    coprimeDispersionGram S β u W A =
      ∑' h : Eisenstein, finitePoissonContribution S {h} β u W A := by
  let F := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a W A h else 0
  have hF (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) : Summable (F a b) := by
    by_cases hab : IsCoprime a b
    · exact (by
        simpa only [F,ite_eq_left hab] using
          (summable_gramDualTerm (hS b hb).1 (hS a ha).1 W hW hW' hA).mul_left
            ((β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)))
    · simp only [F,ite_eq_right hab]
      exact summable_zero
  have hswap : (∑' h : Eisenstein, finitePoissonContribution S {h} β u W A) =
      ∑ a ∈ S, ∑ b ∈ S, ∑' h : Eisenstein, F a b h := by
    simp only [finitePoissonContribution,Finset.sum_singleton]
    change (∑' h : Eisenstein, ∑ a ∈ S, ∑ b ∈ S, F a b h) = _
    rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hF a b ha hb))]
    apply Finset.sum_congr rfl
    intro a ha
    exact Summable.tsum_finsetSum (fun b hb => hF a b ha hb)
  rw [hswap]
  unfold coprimeDispersionGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,F]
    rw [dispersion_pair_poisson (hS a ha).1 (hS b hb).1 (hS a ha).2 (hS b hb).2
      hab β u W hW hW' hA,tsum_mul_left]
    simp only [star_mul]
    ring
  · simp only [ite_eq_right hab,F,tsum_zero]

theorem divisorCoprimeDispersionGram_poisson {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    divisorCoprimeDispersionGram d S β u W A =
      ∑' h : Eisenstein, finiteDivisorPoissonContribution d S {h} β u W A := by
  have hdN := norm_pos_of_ne_zero hd
  rw [divisorCoprimeDispersionGram,coprimeDispersionGram_poisson_lattice S hS
    _ u W hW hW' (show 0 < A/(norm d)^2 by positivity)]
  apply tsum_congr
  intro h
  exact (finiteDivisorPoissonContribution_twist d S {h} β u W A).symm

lemma finiteDivisorPoissonContribution_zero (d : Eisenstein) (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ a ≠ 1)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    finiteDivisorPoissonContribution d S {0} β u W A = 0 := by
  simp only [finiteDivisorPoissonContribution,Finset.sum_singleton]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  by_cases hab : IsCoprime a b
  · have hne : b ≠ a := by
      intro hba
      exact (hS a ha).2.2 (primary_unit_eq_one (isCoprime_self.mp (hba ▸ hab)) (hS a ha).1)
    rw [ite_eq_left hab,gramDualTerm_zero (hS b hb).1 (hS a ha).1
      (hS b hb).2.1 (hS a ha).2.1 hab.symm hne W (A/(norm d)^2)]
    ring
  · exact ite_eq_right hab

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonOuterPowers
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The power saving supplied by a genuinely shortened common-factor
row. This step uses only the scale inequalities of the application. -/
noncomputable section
namespace CubicFirstMoment

lemma shortened_poisson_polynomial {L A N δ η : ℝ}
    (hL : 1 ≤ L) (hA : 0 < A) (hN : 0 ≤ N) (hδ : 0 < δ)
    (hηδ : η ≤ δ) (hAL : L^(1-η) ≤ A) (hNL : N ≤ L^(1-δ)) :
    N+A^(1/3:ℝ)*N+A^(2/3:ℝ)*N^(2/3:ℝ) ≤
      3*A^(2/3:ℝ)*L^(2/3:ℝ)*L^(-δ/3) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hfactor : L^(2/3:ℝ)*L^(-δ/3) = L^(2/3-δ/3) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  have hA2 : L^((1-η)*(2/3:ℝ)) ≤ A^(2/3:ℝ) := by
    rw [Real.rpow_mul hLp.le]
    exact Real.rpow_le_rpow (by positivity) hAL (by norm_num)
  have hA1 : L^((1-η)*(1/3:ℝ)) ≤ A^(1/3:ℝ) := by
    rw [Real.rpow_mul hLp.le]
    exact Real.rpow_le_rpow (by positivity) hAL (by norm_num)
  have h1 : N ≤ A^(2/3:ℝ)*L^(2/3-δ/3) := by
    calc
      _ ≤ L^((1-η)*(2/3:ℝ)+(2/3-δ/3)) := hNL.trans
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
      _ = L^((1-η)*(2/3:ℝ))*L^(2/3-δ/3) := Real.rpow_add hLp _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hA2 (by positivity)
  have h2' : N ≤ A^(1/3:ℝ)*L^(2/3-δ/3) := by
    calc
      _ ≤ L^((1-η)*(1/3:ℝ)+(2/3-δ/3)) := hNL.trans
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
      _ = L^((1-η)*(1/3:ℝ))*L^(2/3-δ/3) := Real.rpow_add hLp _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hA1 (by positivity)
  have h2 : A^(1/3:ℝ)*N ≤ A^(2/3:ℝ)*L^(2/3-δ/3) := by
    have hh := mul_le_mul_of_nonneg_left h2' (Real.rpow_nonneg hA.le (1/3))
    have he : A^(1/3:ℝ)*A^(1/3:ℝ) = A^(2/3:ℝ) := by
      rw [← Real.rpow_add hA]; norm_num
    simpa only [← mul_assoc,he] using hh
  have h3 : A^(2/3:ℝ)*N^(2/3:ℝ) ≤ A^(2/3:ℝ)*L^(2/3-δ/3) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ (L^(1-δ))^(2/3:ℝ) := Real.rpow_le_rpow hN hNL (by norm_num)
      _ = L^((1-δ)*(2/3:ℝ)) := (Real.rpow_mul hLp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  rw [mul_assoc (3*A^(2/3:ℝ)),hfactor]
  linarith

lemma common_outer_scale_small_power {B Q L A δ : ℝ}
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQL : Q ≤ L) (hL : 1 ≤ L)
    (hA : 1 ≤ A) (hδ : 0 < δ) :
    (B*Q^2*L^3/A)^(δ/100) ≤ B^(δ/100)*L^(δ/20) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hP : B*Q^2*L^3/A ≤ B*L^5 := by
    calc
      _ ≤ B*Q^2*L^3 := div_le_self (by positivity) hA
      _ ≤ B*L^2*L^3 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ hQL 2) hB) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (B*L^5)^(δ/100) := Real.rpow_le_rpow (by positivity) hP (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hB (by positivity),← Real.rpow_natCast L 5,← Real.rpow_mul hLp.le]
      congr 2
      norm_num
      ring

lemma commonOuterCost_power_saving (W : ℝ → ℂ) {C B Q A L δ η : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQL : Q ≤ L)
    (hL : 1 ≤ L) (hA : 0 < A) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hηδ : η ≤ δ) (hAL : L^(1-η) ≤ A) :
    commonOuterCost W C (δ/100) B Q A L (L^δ) ≤
      (‖normProfileFourier W 0‖/9)*A+
        3*C*B^(δ/100)*A^(2/3:ℝ)*L^(2/3:ℝ)*L^(-δ/4) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA1 : 1 ≤ A := (Real.one_le_rpow hL (by linarith : 0 ≤ 1-η)).trans hAL
  have hmax : max 1 (L/L^δ) = L^(1-δ) := by
    have he : L/L^δ = L^(1-δ) := by rw [Real.rpow_sub hLp,Real.rpow_one]
    rw [he]
    exact max_eq_right (Real.one_le_rpow hL (by linarith))
  unfold commonOuterCost
  rw [hmax]
  apply add_le_add le_rfl
  have hp := common_outer_scale_small_power hB hQ hQL hL hA1 hδ
  have hb := shortened_poisson_polynomial hL hA (by positivity) hδ hηδ hAL le_rfl
  calc
    _ ≤ C*(B^(δ/100)*L^(δ/20))*(3*A^(2/3:ℝ)*L^(2/3:ℝ)*L^(-δ/3)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hC) hb (by positivity) (by positivity)
    _ = (3*C*B^(δ/100)*A^(2/3:ℝ)*L^(2/3:ℝ))*L^(δ/20-δ/3) := by
      rw [Real.rpow_sub hLp,show -δ/3 = -(δ/3) by ring,Real.rpow_neg hLp.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightDivisorBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular common-divisor mass: exact empty row, rough-divisor
split, and shortened outer-sieve bound. The constants do not depend on the
angular index, since its coefficient factors have modulus one. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

theorem angular_fullPrime_divisor_noncoprime_log_saving {R c η : ℝ} (hR : 1 ≤ R)
    (hc : 0 < c) (hc1 : c ≤ 1) (hηc : η ≤ c)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (d e : Eisenstein) (u : ℝ), T₀ ≤ L r → 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → (∀ i, (L r)^c < X i) →
      primary d → norm d ≤ L r → (L r)^(1-η) ≤ A →
      A ≤ (L r)^2/(1+Real.log (L r))^G →
      ‖divisorDispersionVariance d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A-
        divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,hC,hbound⟩ := fullPrime_divisor_noncoprime_outer (ι := ι)
    (show 0 < c/100 by positivity) (show c/100 ≤ 1 by linarith) hR V hV hV'
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (show 0 < c/4 by positivity) (a+k))
  let B := R^Fintype.card ι
  let F := (2:ℝ)^(3*Fintype.card ι)
  let K₀ := ‖normProfileFourier V 0‖/9
  let K₁ := K₀*F*(E+1)+3*C*B^(c/100)*F*(E+1)+1
  refine ⟨3*(a+k),K₁,T₀,by dsimp [K₁,K₀,F,B]; positivity,?_⟩
  intro r X A d e u hT₀ hL hX hprod hrough hd hdL hAlo hAhi
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hz1 : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hz : 0 < 1+Real.log (L r) := zero_lt_one.trans_le hz1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hh := hbound (W r) X (L r) ((L r)^c) A e d
    (angularHeightPrimeCoefficient ℓ R (W r) X) u (fun i => zero_lt_one.trans_le (hX i)) hprod hL
    (Real.one_le_rpow hL hc.le) hA hd (hlo r) (hhi r) hrough
  have hcost := commonOuterCost_power_saving V hC.le hB (norm_nonneg d) hdL
    hL hA hc hc1 hηc hAlo
  have he : (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      ‖angularHeightPrimeCoefficient ℓ R (W r) X b‖^2) ≤ (E+1)*L r*(1+Real.log (L r))^a := by
    rw [angularHeightPrimeCoefficient_energy]
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans
    apply (henergy r X hL hX hprod).trans
    nlinarith [mul_nonneg hLp.le (pow_nonneg hz.le a)]
  have hlattice := cube_lattice_error_scale hA hLp hz a k hAhi
  have hlog : (1+Real.log (L r))^a*(L r)^(-c/4) ≤ 1/(1+Real.log (L r))^k := by
    rw [show -c/4 = -(c/4) by ring]
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  have hpower : (L r)^(2/3:ℝ)*L r = (L r)^(5/3:ℝ) := by
    calc
      _ = (L r)^(2/3:ℝ)*(L r)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hLp]; norm_num
  have hsplit : ((K₀*A+3*C*B^(c/100)*A^(2/3:ℝ)*(L r)^(2/3:ℝ)*(L r)^(-c/4))*F)*
      ((E+1)*L r*(1+Real.log (L r))^a) =
      (K₀*F*(E+1))*(A*L r*(1+Real.log (L r))^a)+
      (3*C*B^(c/100)*F*(E+1))*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
        ((1+Real.log (L r))^a*(L r)^(-c/4)) := by
    rw [← hpower]
    ring
  apply (hh.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost (by positivity))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left he (by positivity)))).trans
  change ((K₀*A+3*C*B^(c/100)*A^(2/3:ℝ)*(L r)^(2/3:ℝ)*(L r)^(-c/4))*F)*
    ((E+1)*L r*(1+Real.log (L r))^a) ≤ _
  rw [hsplit]
  calc
    _ ≤ (K₀*F*(E+1))*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k)+
        (3*C*B^(c/100)*F*(E+1))*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
          (1/(1+Real.log (L r))^k) := add_le_add
      (mul_le_mul_of_nonneg_left hlattice (by dsimp [K₀,F]; positivity))
      (mul_le_mul_of_nonneg_left hlog (by dsimp [F,B]; positivity))
    _ = (K₀*F*(E+1)+3*C*B^(c/100)*F*(E+1))*
        (A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ K₁*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [K₁]
      linarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorPoissonSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cube/noncube splitting of the coprime square-divisor component. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tsum_split_effective_cubes (d : Eisenstein) (F : Eisenstein → ℂ)
    (hF : Summable F) (h0 : F 0 = 0) :
    (∑' h : Eisenstein, F h) =
      (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h) then F h else 0) +
      (∑' h : Eisenstein, if ∃ j : Eisenstein, j^3 = d*h then 0 else F h) := by
  let P := fun h : Eisenstein => h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h)
  let Q := fun h : Eisenstein => ¬∃ j : Eisenstein, j^3 = d*h
  have hp := hF.indicator {h | P h}
  have hq := hF.indicator {h | Q h}
  have he (h : Eisenstein) : F h = {h | P h}.indicator F h+{h | Q h}.indicator F h := by
    by_cases hz : h = 0
    · subst h
      simp only [h0,Set.indicator_apply,ite_self,zero_add]
    · by_cases hc : ∃ j : Eisenstein, j^3 = d*h
      · rw [Set.indicator_of_mem (show h ∈ {h | P h} from ⟨hz,hc⟩),
          Set.indicator_of_notMem (show h ∉ {h | Q h} from fun hn => hn hc),add_zero]
      · rw [Set.indicator_of_notMem (show h ∉ {h | P h} from fun hp => hc hp.2),
          Set.indicator_of_mem (show h ∈ {h | Q h} from hc),zero_add]
  rw [tsum_congr he,hp.tsum_add hq]
  congr 1
  · apply tsum_congr
    intro h
    by_cases hh : P h
    · rw [Set.indicator_of_mem (show h ∈ {h | P h} from hh),ite_eq_left hh]
    · rw [Set.indicator_of_notMem (show h ∉ {h | P h} from hh),ite_eq_right hh]
  · apply tsum_congr
    intro h
    by_cases hc : ∃ j : Eisenstein, j^3 = d*h
    · rw [Set.indicator_of_notMem (show h ∉ {h | Q h} from fun hn => hn hc),ite_eq_left hc]
    · rw [Set.indicator_of_mem (show h ∈ {h | Q h} from hc),ite_eq_right hc]

theorem divisorCubePoissonContribution_lattice {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    divisorCubePoissonContribution d S β u V A =
      ∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h) then
        finiteDivisorPoissonContribution d S {h} β u V A else 0 := by
  let P := fun h : Eisenstein => h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h)
  let F := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*
        (mixedSymbol b a (d^2)*gramDualTerm b a V (A/(norm d)^2) h) else 0
  have hF (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) :
      Summable (fun h => if P h then F a b h else 0) := by
    by_cases hab : IsCoprime a b
    · have hdN := norm_pos_of_ne_zero hd
      have hs := ((summable_gramDualTerm (hS b hb) (hS a ha) V hV hV'
        (show 0 < A/(norm d)^2 by positivity)).mul_left
        ((β a*normTwist u a)*star (β b*normTwist u b)*
          ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*mixedSymbol b a (d^2))).indicator {h | P h}
      convert hs using 1
      all_goals try with_reducible_and_instances rfl
      funext h
      rw [Set.indicator_apply]
      change (if P h then F a b h else 0) = if P h then _ else 0
      split_ifs
      · simp only [F,ite_eq_left hab]
        ring
      · rfl
    · simp only [F,ite_eq_right hab,ite_self]
      exact summable_zero
  have he (h : Eisenstein) : (if P h then finiteDivisorPoissonContribution d S {h} β u V A else 0) =
      ∑ a ∈ S, ∑ b ∈ S, if P h then F a b h else 0 := by
    by_cases hp : P h
    · simp only [hp,ite_true, if_true,finiteDivisorPoissonContribution,Finset.sum_singleton,F]
    · simp only [hp,ite_false, if_false,Finset.sum_const_zero]
  change _ = ∑' h : Eisenstein, if P h then _ else 0
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hF a b ha hb))]
  unfold divisorCubePoissonContribution
  apply Finset.sum_congr rfl
  intro a ha
  rw [Summable.tsum_finsetSum (fun b hb => hF a b ha hb)]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    change ((β a*normTwist u a)*star (β b*normTwist u b)*
      ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ))*
      (if P h then mixedSymbol b a (d^2)*gramDualTerm b a V (A/(norm d)^2) h else 0) =
      if P h then F a b h else 0
    by_cases hp : P h
    · simp only [hp,ite_true, if_true,F,ite_eq_left hab]
    · simp only [hp,ite_false, if_false,mul_zero]
  · simp only [ite_eq_right hab,F,ite_self,tsum_zero]

theorem divisorCoprimeDispersionGram_split {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ a ≠ 1)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    divisorCoprimeDispersionGram d S β u V A =
      divisorCubePoissonContribution d S β u V A + divisorNoncubePoissonContribution d hd S β u V A := by
  rw [divisorCoprimeDispersionGram_poisson hd S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
    β u V hV hV' hA,
    divisorCubePoissonContribution_lattice hd S (fun a ha => (hS a ha).1) β u V hV hV' hA,
    divisorNoncubePoissonContribution_lattice hd S (fun a ha => (hS a ha).1) β u V hV hV' hA]
  exact tsum_split_effective_cubes d _
    (summable_finiteDivisorPoisson_singleton hd S (fun a ha => (hS a ha).1) β u V hV hV' hA)
    (finiteDivisorPoissonContribution_zero d S hS β u V A)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeSmallCoprime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A divisor smaller than every supported prime is coprime to every
actual squarefree prime-product coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_coprime_small_element {R D : ℝ}
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e d : Eisenstein) (hd : d ≠ 0) (hsmall : norm d ≤ D)
    {a : Eisenstein} (ha : a ∈ fullSquarefreePrimeSupport R W X e) : IsCoprime a d := by
  have hprim := fullSquarefreePrimeSupport_primary R W X e ha
  by_contra hcop
  obtain ⟨p,hp,hpd⟩ := not_coprime_prime_cover hprim.1 hprim.2 hcop
  have hpp := (primaryPrimeFactor_spec hprim.1 hp).1
  obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R W X hpp
    (primaryPrimeFactor_spec hprim.1 hp).2 (Finset.mem_filter.mp ha).1
  have hw := ((fullPrimeSupport_mem_iff W X hX hhi i p).mp hi).2
  have hratio : 1 ≤ norm p/X i := le_of_not_gt (fun h => hw (hlo i _ h))
  have hn : X i ≤ norm p := by simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hratio
  have hpD : norm p ≤ D := (norm_le_of_dvd hd hpd).trans hsmall
  exact (not_lt_of_ge (hn.trans hpD)) (hrough i)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDivisorGramAsymptotic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coprime component of the actual square-divisor variance has
the same cube model, multiplied by its exact divisor density. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_divisor_coprime_gram_asymptotic (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (d e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      primary d → Squarefree d → norm d ≤ (L r)^(η/16) → norm d ≤ (L r)^c →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hnoncube⟩ := angular_divisor_noncube_total_saving ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k U
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨Kn,Tn,hKn,hn⟩ := hnoncube L W hL hW hlo hhi
  obtain ⟨G,Kc,Tc,hKc,hcube⟩ := angular_cube_poisson_log_saving ℓ hR hc hW hlo hhi V hV hV' k
  refine ⟨G,Kn+Kc,max 2 (max Tn Tc),by positivity,?_⟩
  intro r X A d e u hT hprod hrough hd hds hdη hdc hAlo hAhi he heN hu
  have hd0 := primary_ne_zero hd
  have hd1 : 1 ≤ norm d := one_le_norm hd0
  have h2 : 2 ≤ L r := (le_max_left _ _).trans hT
  have hLp : 0 < L r := by linarith
  have hz : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hAp : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hA₂ : A ≤ (L r)^2 := hAhi.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hz))
  have hX : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith : (1:ℝ) ≤ 2*L r) hc.le).trans (hrough i).le
  have hrough' : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hrough i)
  have hS (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R (W r) X e) :
      primary a ∧ Squarefree a ∧ a ≠ 1 := by
    have hp := fullSquarefreePrimeSupport_primary R (W r) X e ha
    refine ⟨hp.1,hp.2,?_⟩
    have hb := (fullPrimeProduct_norm_bounds R (W r) X
      (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) (Finset.mem_filter.mp ha).1).1
    rw [hprod] at hb
    intro ha1
    rw [ha1,norm_one_eq] at hb
    linarith
  have hcop (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R (W r) X e) : IsCoprime a d :=
    fullPrime_coprime_small_element (W r) X (fun i => zero_lt_one.trans_le (hX i))
      (hlo r) (hhi r) hrough' e d hd0 hdc ha
  have hTn : Tn ≤ L r := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTc : Tc ≤ L r := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hn' := hn r X A d e u hd0 hTn hprod hrough hdη hAlo hA₂ he heN hu
  have hc' := hcube r X A e u hTc (hL r) hX hprod hrough' hAp hAhi
  have hcube' :
      ‖divisorCubePoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
      Kc*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
    rw [divisorCubePoissonContribution_eq hd hds _ (fun a ha => ⟨(hS a ha).1,hcop a ha⟩)
      _ _ _ hAp.le,← mul_sub,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ 1/(norm d)^2 by positivity)]
    apply (mul_le_of_le_one_left (_root_.norm_nonneg _) _).trans hc'
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ hd1 : 1 ≤ (norm d)^2)
  rw [divisorCoprimeDispersionGram_split hd0 _ hS _ _ _ hV hV' hAp]
  calc
    _ = ‖(divisorCubePoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A) +
        divisorNoncubePoissonContribution d hd0 (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hcube' hn').trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDivisorModelAsymptotic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore all pairs in the model polynomial of the square-divisor
coprime variance. The model is now the literal squared finite sum. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_divisor_coprime_model_asymptotic (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (d e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      primary d → Squarefree d → norm d ≤ (L r)^(η/16) → norm d ≤ (L r)^c →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hgram⟩ := angular_divisor_coprime_gram_asymptotic ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k U
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨G,K₁,T₁,hK₁,hgram⟩ := hgram L W hL hW hlo hhi
  obtain ⟨K₂,T₂,hK₂,hmodel⟩ := angular_cube_model_overlap_log_saving ℓ hR hc hW hlo hhi V k
  refine ⟨G,K₁+K₂,max T₁ T₂,by positivity,?_⟩
  intro r X A d e u hT hprod hrough hd hds hdη hdc hAlo hAhi he heN hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hX : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hrough i).le
  have hrough' : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hrough i)
  have hg := hgram r X A d e u ((le_max_left _ _).trans hT) hprod hrough hd hds hdη hdc
    hAlo hAhi he heN hu
  have hm := hmodel r X A e u ((le_max_right _ _).trans hT) (hL r) hX hprod hrough' hA.le
  have hcoeff : 1/(norm d)^2 ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (one_le_norm (primary_ne_zero hd)) : 1 ≤ (norm d)^2)
  have hm' :
      ‖(1/(norm d)^2:ℝ)*
        (coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A)‖ ≤
      K₂*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ 1/(norm d)^2 by positivity),
      norm_sub_rev]
    exact (mul_le_of_le_one_left (_root_.norm_nonneg _) hcoeff).trans hm
  calc
    _ = ‖(divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A) +
        (1/(norm d)^2:ℝ)*(coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hg hm').trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDivisorFullModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full small-square-divisor variance has the literal squared
model. This adds the proved noncoprime remainder to the coprime model. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_divisor_full_model_asymptotic (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (d e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      primary d → Squarefree d → norm d ≤ (L r)^(η/16) → norm d ≤ (L r)^c →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖divisorDispersionVariance d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A-
        (1/(norm d)^2:ℝ)*cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η₀,σ,hη₀,hη₀1,hσ,hgram⟩ := angular_divisor_coprime_model_asymptotic ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ V hV hV' k U
  let η := min η₀ c
  have hη : 0 < η := lt_min hη₀ hc
  have hη0 : η ≤ η₀ := min_le_left _ _
  have hηc : η ≤ c := min_le_right _ _
  have hη1 : η ≤ 1 := hη0.trans hη₀1
  refine ⟨η,σ,hη,hη1,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨G₁,K₁,T₁,hK₁,hgram⟩ := hgram L W hL hW hlo hhi
  obtain ⟨G₂,K₂,T₂,hK₂,hcommon⟩ := angular_fullPrime_divisor_noncoprime_log_saving ℓ
    hR hc hc1 (show η/16 ≤ c by linarith) hW hlo hhi V hV hV' k
  refine ⟨G₁+G₂,K₁+K₂,max T₁ T₂,by positivity,?_⟩
  intro r X A d e u hT hprod hrough hd hds hdη hdc hAlo hAhi he heN hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz1 : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hz : 0 < 1+Real.log (L r) := zero_lt_one.trans_le hz1
  have hcut (n : ℕ) (hn : n ≤ G₁+G₂) : A ≤ (L r)^2/(1+Real.log (L r))^n :=
    hAhi.trans (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hz n)
      (pow_le_pow_right₀ hz1 hn))
  have hX : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hrough i).le
  have hrough' : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hrough i)
  have hdL : norm d ≤ L r := hdη.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (hL r) (show η/16 ≤ 1 by linarith))
  have hc' := hcommon r X A d e u ((le_max_right _ _).trans hT) (hL r) hX hprod
    hrough' hd hdL hAlo (hcut G₂ (Nat.le_add_left _ _))
  have hg := hgram r X A d e u ((le_max_left _ _).trans hT) hprod hrough hd hds
    (hdη.trans (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith))) hdc
    ((Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith)).trans hAlo)
    (hcut G₁ (Nat.le_add_right _ _)) he heN hu
  have htri : ∀ a b c : ℂ, ‖a-c‖ ≤ ‖a-b‖+‖b-c‖ := by
    intro a b c
    calc
      _ = ‖(a-b)+(b-c)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  exact (htri _ _ _).trans ((add_le_add hc' hg).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The residue sum after squarefree majorization

The actual collected coefficients agree with Möbius below the truncation.
Their uniformly convergent norm series therefore differs from the true
Möbius residue by `O(D⁻¹ᐟ²)`.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeTruncation_spec (D : ℝ) :
    ∀ c ∈ squarefreeDivisorTruncation D, primary c ∧ Squarefree c := by
  intro c hc
  exact ⟨(mem_squarefreeDivisorTruncation.mp hc).1,(mem_squarefreeDivisorTruncation.mp hc).2.1⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SievedModelAssembly
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite sieve assembly and its error norm. These identities
retain the actual joined square divisors and their Möbius weights. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma collectedSieve_weighted_sum (C : Finset Eisenstein) (F : Eisenstein → ℂ) :
    (∑ d ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
      (collectedSquarefreeSieveCoefficient C d:ℂ)*F d) =
    ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*F (primarySquarefreeJoin c d) := by
  let J := fun t : Eisenstein × Eisenstein => primarySquarefreeJoin t.1 t.2
  let v := fun t : Eisenstein × Eisenstein => (idealMoebius t.1:ℂ)*(idealMoebius t.2:ℂ)
  have hf := Finset.sum_fiberwise_of_maps_to (s := C.product C) (t := (C.product C).image J)
    (g := J) (fun t ht => Finset.mem_image_of_mem J ht) (fun t => v t*F (J t))
  calc
    _ = ∑ d ∈ (C.product C).image J,
        ∑ t ∈ (C.product C).filter (fun t => J t = d), v t*F (J t) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [collectedSquarefreeSieveCoefficient,Complex.ofReal_sum,Complex.ofReal_mul,
        Complex.ofReal_intCast,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [v,J]
      rw [(Finset.mem_filter.mp ht).2]
    _ = ∑ t ∈ C.product C, v t*F (J t) := hf
    _ = _ := Finset.sum_product _ _ _

lemma sievedDispersionVariance_pair_sum (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    sievedDispersionVariance C S β u W A =
      ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
        divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A := by
  rw [sievedDispersionVariance_eq C hC S hS β u W hW hW' hA]
  exact collectedSieve_weighted_sum C _

lemma finiteSieve_model_identity (C : Finset Eisenstein) (M : ℂ) :
    (finiteSieveDensity C:ℂ)*M =
      ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
        ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M := by
  simp only [finiteSieveDensity,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_intCast,Complex.ofReal_one,Complex.ofReal_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma sieved_model_error_bound (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A)
    (M : ℂ) {E : ℝ}
    (herror : ∀ c ∈ C, ∀ d ∈ C,
      ‖divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A-
        ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M‖ ≤ E) :
    ‖sievedDispersionVariance C S β u W A-(finiteSieveDensity C:ℂ)*M‖ ≤
      (C.card:ℝ)^2*E := by
  rw [sievedDispersionVariance_pair_sum C hC S hS β u W hW hW' hA,
    finiteSieve_model_identity,← Finset.sum_sub_distrib]
  have hs (c : Eisenstein) (hc : c ∈ C) :
      ‖(∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
        divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A)-
        ∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
          ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M‖ ≤ ∑ _d ∈ C, E := by
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro d hd
    rw [show (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
        divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A-
        (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
          ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M =
        ((idealMoebius c:ℂ)*(idealMoebius d:ℂ))*
          (divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A-
            ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M) by ring,
      norm_mul,norm_mul]
    apply (mul_le_of_le_one_left (_root_.norm_nonneg _) _).trans (herror c hc d hd)
    simpa only [one_mul] using mul_le_mul (norm_idealMoebius_le_one c)
      (norm_idealMoebius_le_one d) (_root_.norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hs).trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveTruncationScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm and cardinality costs of the logarithmic square-divisor
truncation used in the positive variance term. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeDivisorTruncation_card_le {D : ℝ} (hD : 0 ≤ D) :
    ((squarefreeDivisorTruncation D).card:ℝ) ≤ 18*D := by
  apply le_trans _ (nonzeroNormBall_card_le hD)
  have hsub : squarefreeDivisorTruncation D ⊆ nonzeroNormBall D := by
    intro c hc
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
  exact_mod_cast Finset.card_le_card hsub

lemma squarefreeTruncation_join_norm {D : ℝ} (hD : 0 ≤ D)
    {c d : Eisenstein} (hc : c ∈ squarefreeDivisorTruncation D)
    (hd : d ∈ squarefreeDivisorTruncation D) :
    norm (primarySquarefreeJoin c d) ≤ D^2 := by
  have hc' := mem_squarefreeDivisorTruncation.mp hc
  have hd' := mem_squarefreeDivisorTruncation.mp hd
  apply (primarySquarefreeJoin_norm_le hc'.1 hd'.1).trans
  exact (mul_le_mul hc'.2.2 hd'.2.2 (norm_nonneg d) hD).trans_eq (by ring)

lemma eventually_logPower_le_rpow {a : ℝ} (ha : 0 < a) (b : ℕ) :
    ∀ᶠ X : ℝ in atTop, (1+Real.log X)^b ≤ X^a := by
  filter_upwards [negative_power_log_saving ha b,eventually_ge_atTop (1:ℝ)] with X hX hX1
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hz : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX1]
  apply (inv_le_inv₀ (Real.rpow_pos_of_pos hXp a) (pow_pos hz b)).mp
  simpa only [Real.rpow_neg hXp.le,one_div] using hX

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSievedFullModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the proved full-variance model over the actual logarithmic
square-divisor sieve. All joined divisors lie in the uniform small
range, and the finite summation costs only a fixed logarithmic power. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_sieved_full_model_asymptotic_oai (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U b : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖sievedDispersionVariance (squarefreeDivisorTruncation ((1+Real.log (L r))^b))
          (fullSquarefreePrimeSupport R (W r) X e) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A-
        (finiteSieveDensity (squarefreeDivisorTruncation ((1+Real.log (L r))^b)):ℂ)*
          cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
            (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη1,hσ,hgram⟩ := angular_divisor_full_model_asymptotic ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ V hV hV' (k+2*b) U
  have ha : 0 < min (η/16) c := lt_min (by positivity) hc
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp (eventually_logPower_le_rpow ha (2*b))
  refine ⟨η,σ,hη,hη1,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨G,K,T₂,hK,hgram⟩ := hgram L W hL hW hlo hhi
  refine ⟨G,324*K,max T₁ T₂,by positivity,?_⟩
  intro r X A e u hT hprod hrough hAlo hAhi he heN hu
  let z := 1+Real.log (L r)
  let D := z^b
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := angularHeightPrimeCoefficient ℓ R (W r) X
  let T := squarefreeDivisorTruncation D
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz1 : 1 ≤ z := by dsimp [z]; linarith [Real.log_nonneg (hL r)]
  have hz : 0 < z := zero_lt_one.trans_le hz1
  have hD : 0 < D := pow_pos hz b
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hsmall : D^2 ≤ (L r)^(min (η/16) c) := by
    simpa only [D,←pow_mul,Nat.mul_comm] using hT₁ (L r) ((le_max_left _ _).trans hT)
  have hjoin (p q : Eisenstein) (hp : p ∈ T) (hq : q ∈ T) :
      norm (primarySquarefreeJoin p q) ≤ (L r)^(min (η/16) c) :=
    (squarefreeTruncation_join_norm hD.le hp hq).trans hsmall
  have herror (p : Eisenstein) (hp : p ∈ T) (q : Eisenstein) (hq : q ∈ T) :
      ‖divisorDispersionVariance (primarySquarefreeJoin p q) S β u V A-
        ((1/(norm (primarySquarefreeJoin p q))^2:ℝ):ℂ)*cubeModelTerm S β u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/z^(k+2*b) := by
    have hp' := squarefreeTruncation_spec D p hp
    have hq' := squarefreeTruncation_spec D q hq
    exact hgram r X A (primarySquarefreeJoin p q) e u ((le_max_right _ _).trans hT)
      hprod hrough (primarySquarefreeJoin_primary hp'.1 hq'.1)
      (primarySquarefreeJoin_squarefree hp'.1 hq'.1)
      ((hjoin p q hp hq).trans (Real.rpow_le_rpow_of_exponent_le (hL r) (min_le_left _ _)))
      ((hjoin p q hp hq).trans (Real.rpow_le_rpow_of_exponent_le (hL r) (min_le_right _ _)))
      hAlo hAhi he heN hu
  have hh := sieved_model_error_bound T (squarefreeTruncation_spec D) S
    (fun a ha => (fullSquarefreePrimeSupport_primary R (W r) X e ha).1)
    β u V hV hV' hA (cubeModelTerm S β u V A) herror
  have hcard : (T.card:ℝ)^2 ≤ (18*D)^2 :=
    pow_le_pow_left₀ (by positivity) (squarefreeDivisorTruncation_card_le hD.le) 2
  apply hh.trans ((mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq ?_)
  change (18*z^b)^2*(K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/z^(k+2*b)) =
    (324*K)*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/z^k
  rw [mul_pow,←pow_mul,show b*2 = 2*b by omega,pow_add]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CubicFirstMoment.angular_sieved_full_model_asymptotic_oai.{u_1, u_2} := @OAI.CubicFirstMoment.angular_sieved_full_model_asymptotic_oai.{u_1, u_2}
