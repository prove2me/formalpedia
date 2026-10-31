-- Prove2me | solution 1 for OAI.CubicFirstMoment.two_prime_transition_centered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:05:39.157672+00:00
-- url     : https://prove2.me/submissions/837ed518-616c-414f-b944-1988cb052f7d

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022
import Theorems.Thm_OAI_CubicFirstMoment_noncube_poisson_total_saving

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
-- module Solutions.OAIQ096_CM.CubicGram_CommonFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebra of fixed angular prime moments

The angular weight is the phase of a nonzero Eisenstein integer raised to
an integer power.  These elementary facts ensure that fixed angular
weights preserve absolute values and distribute through finite prime sums.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

/-- The bias constant in the manuscript is strictly positive. -/
theorem cStar_pos : 0 < cStar := by
  unfold cStar
  positivity

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem primaryCharacterGram_self {b : Eisenstein} (hb : primary b)
    (W : ℝ → ℂ) (A : ℝ) :
    primaryCharacterGram b b W A =
      ∑' a : Eisenstein, if primary a ∧ IsCoprime b a then W (norm a/A) else 0 := by
  unfold primaryCharacterGram
  apply tsum_congr
  intro a
  by_cases ha : primary a
  · simp only [ha, true_and, ite_true, if_true]
    by_cases hba : IsCoprime b a
    · have hc : cubicSymbol b a * star (cubicSymbol b a) = 1 := by
        have h := Complex.mul_conj' (cubicSymbol b a)
        simp only [starRingEnd_apply, norm_cubicSymbol_of_isCoprime hb hba] at h
        simpa using h
      rw [ite_eq_left hba, mul_assoc, hc, mul_one]
    · simp [hba, cubicSymbol_eq_zero_of_not_isCoprime hb hba]
  · simp [ha]

theorem dispersionAmplitude_mul_star {b : Eisenstein} (hb : primary b)
    (hsb : Squarefree b) (β : Eisenstein → ℂ) (u : ℝ) :
    dispersionAmplitude β u b * star (dispersionAmplitude β u b) = ((‖β b‖^2 : ℝ) : ℂ) := by
  have h := Complex.mul_conj' (dispersionAmplitude β u b)
  simp only [starRingEnd_apply] at h
  rw [h]
  simp only [dispersionAmplitude, norm_mul, norm_normTwist, mul_one, norm_gauss hb,
    ite_eq_left hsb, Complex.ofReal_pow]

/-- The exact diagonal retains the coprimality condition in the lattice count. -/
theorem dispersion_diagonal (B : Finset Eisenstein) (hB : ∀ b ∈ B, primary b)
    (hsB : ∀ b ∈ B, Squarefree b) (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    (∑ b ∈ B, dispersionAmplitude β u b * star (dispersionAmplitude β u b) *
      primaryCharacterGram b b W A) =
      ∑ b ∈ B, ((‖β b‖^2 : ℝ) : ℂ) *
        ∑' a : Eisenstein, if primary a ∧ IsCoprime b a then W (norm a/A) else 0 := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [dispersionAmplitude_mul_star (hB b hb) (hsB b hb), primaryCharacterGram_self (hB b hb)]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SievedDispersion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual short Möbius, zeta and logarithmic factors occurring in
the finite ideal convolution identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryElementBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((primaryElementBall X).card : ℝ) ≤ 18*X :=
  (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (nonzeroNormBall_card_le hX)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeSlice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quotient support for divisor-restricted prime coefficients.
No independent-prime condition is asserted for the shortened coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeCoefficient_norm_bound (R : ℝ) (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (b : Eisenstein) :
    ‖fullPrimeCoefficient R W X b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hs : Squarefree b
  · simpa only [fullPrimeCoefficient,squarefreeConvolution,ite_eq_left hs] using
      orderedConvolution_norm_bound (fullPrimeSupport R W X)
        (fun i n => W i (norm n/X i)) M
        (fun i p hp => fullPrimeSupport_prime R W X i p hp) hM
        (fun i p _ => hW i _) b
  · simp only [fullPrimeCoefficient,squarefreeConvolution,ite_eq_right hs,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductPolynomialBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height-independent bounds for the actual two full prime convolutions.
These are used only beyond the power range of the published height mean. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma fullPrimeProduct_centered (R : ℝ) (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
    (XA : κ → ℝ) (XB : ι → ℝ) (u : ℝ) :
    centeredProductPolynomial (fullSquarefreePrimeSupport R WA XA 1)
      (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) 0 u =
      fullPrimeProductGauss R WA WB XA XB u-fullPrimeProductModel R WA WB XA XB u := by
  unfold centeredProductPolynomial fullPrimeProductGauss fullPrimeProductModel
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  simp only [theta_zero, mul_one,centeredGauss]
  ring

lemma fullPrimeProduct_weighted_bound (R : ℝ) (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
    (XA : κ → ℝ) (XB : ι → ℝ) {M : ℝ}
    (F : Eisenstein → Eisenstein → ℂ)
    (hF : ∀ a ∈ fullSquarefreePrimeSupport R WA XA 1,
      ∀ b ∈ fullSquarefreePrimeSupport R WB XB 1, ‖F a b‖ ≤ M) :
    ‖∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
      ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
        fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*F a b‖ ≤
      (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1, ‖fullPrimeCoefficient R WA XA a‖)*
        (∑ b ∈ fullSquarefreePrimeSupport R WB XB 1, ‖fullPrimeCoefficient R WB XB b‖)*M := by
  calc
    _ ≤ ∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
        ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
          ‖fullPrimeCoefficient R WA XA a‖*‖fullPrimeCoefficient R WB XB b‖*M := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_left (hF a ha b hb) (by positivity)
    _ = _ := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeUpper
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary counting upper bound needed in the smooth-number
Rankin argument, derived from the existing ordinary prime PNT input. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma primaryPrimeCount_mono {x y : ℝ} (hxy : x ≤ y) :
    primaryPrimeCount x ≤ primaryPrimeCount y := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,hpx⟩ := mem_primeCutoff.mp hp
  exact mem_primeCutoff.mpr ⟨hp,hpx.trans hxy⟩

theorem primaryPrimeCount_upper (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      primaryPrimeCount Y ≤ C*Y/Real.log Y := by
  have hevent : ∀ᶠ Y : ℝ in atTop,
      primaryPrimeCount Y*Real.log Y/Y < 2 :=
    hpnt.eventually (eventually_lt_nhds (by norm_num : (1:ℝ) < 2))
  obtain ⟨Y₀,hY₀⟩ := eventually_atTop.mp hevent
  let Q := max 2 Y₀
  let C := 2+primaryPrimeCount Q
  have hc : 0 ≤ primaryPrimeCount Q := Nat.cast_nonneg _
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro Y hY
  have hY1 : 1 < Y := lt_of_lt_of_le (by norm_num) hY
  have hY0 : 0 < Y := zero_lt_one.trans hY1
  have hl : 0 < Real.log Y := Real.log_pos hY1
  apply (le_div_iff₀ hl).mpr
  by_cases hQ : Q ≤ Y
  · have h := (div_lt_iff₀ hY0).mp (hY₀ Y ((le_max_right 2 Y₀).trans hQ))
    apply h.le.trans
    apply mul_le_mul_of_nonneg_right _ hY0.le
    dsimp [C]
    linarith
  · have hcount := primaryPrimeCount_mono (le_of_not_ge hQ)
    have hCQ : primaryPrimeCount Q ≤ C := by dsimp [C]; linarith
    calc
      primaryPrimeCount Y*Real.log Y ≤ C*Real.log Y :=
        mul_le_mul_of_nonneg_right (hcount.trans hCQ) hl.le
      _ ≤ C*Y := mul_le_mul_of_nonneg_left (Real.log_le_self hY0.le) hC.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductSharpMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime-counting savings in the actual coefficients of an
exceptional triple. These are consequences of the ordinary prime PNT;
no moment estimate for the new paper is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_subset_primeCutoff (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (i : ι) : fullPrimeSupport R W X i ⊆ primeCutoff (R*X i) := by
  intro p hp
  obtain ⟨hpre,hq⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb,_hw⟩ := Finset.mem_filter.mp hpre
  exact mem_primeCutoff.mpr ⟨⟨(mem_primaryElementBall.mp hb).1,hq⟩,
    (mem_primaryElementBall.mp hb).2⟩

lemma fullSquarefreePrimeSupport_card_le_product (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (e : Eisenstein) :
    ((fullSquarefreePrimeSupport R W X e).card:ℝ) ≤
      ∏ i, ((fullPrimeSupport R W X i).card:ℝ) := by
  calc
    _ ≤ ((orderedConvolutionSupport (fullPrimeSupport R W X)).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    _ ≤ ((Fintype.piFinset (fullPrimeSupport R W X)).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_image_le)
    _ = _ := by rw [Fintype.card_piFinset,Nat.cast_prod]

omit [Fintype ι] [DecidableEq ι] in
theorem fullPrimeSupport_card_log_bound (hpnt : PrimaryPrimePNT) {R : ℝ} (hR : 1 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (L : ℝ),
      0 < L → (∀ i, 2 ≤ X i) → (∀ i, L ≤ Real.log (X i)) →
      ∀ i, ((fullPrimeSupport R W X i).card:ℝ) ≤ K*X i/L := by
  obtain ⟨C,hC,hcount⟩ := primaryPrimeCount_upper hpnt
  refine ⟨C*R,mul_pos hC (zero_lt_one.trans_le hR),?_⟩
  intro W X L hL hX hlog i
  have hXp : 0 < X i := lt_of_lt_of_le (by norm_num) (hX i)
  have hRX : 2 ≤ R*X i := (hX i).trans
    (le_mul_of_one_le_left hXp.le hR)
  have hlogRX : L ≤ Real.log (R*X i) := (hlog i).trans
    (Real.log_le_log hXp (le_mul_of_one_le_left hXp.le hR))
  calc
    _ ≤ primaryPrimeCount (R*X i) := Nat.cast_le.mpr
      (Finset.card_le_card (fullPrimeSupport_subset_primeCutoff R W X i))
    _ ≤ C*(R*X i)/Real.log (R*X i) := hcount _ hRX
    _ ≤ C*(R*X i)/L := div_le_div_of_nonneg_left (by positivity) hL hlogRX
    _ = _ := by ring

theorem fullPrimeCoefficient_sharp_moments (hpnt : PrimaryPrimePNT)
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (L : ℝ),
      0 < L → (∀ i, 2 ≤ X i) → (∀ i, L ≤ Real.log (X i)) →
      (∀ i x, ‖W i x‖ ≤ 1) → ∀ e : Eisenstein,
      (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖) ≤
          K*(∏ i, X i)/L^(Fintype.card ι) ∧
      (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2) ≤
          K*(∏ i, X i)/L^(Fintype.card ι) := by
  obtain ⟨C,hC,hcard⟩ := fullPrimeSupport_card_log_bound (ι := ι) hpnt hR
  let n := Fintype.card ι
  let M : ℝ := (n^n:ℕ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨(M+1)^2*C^n,by positivity,?_⟩
  intro W X L hL hX hlog hW e
  have hbound (b : Eisenstein) : ‖fullPrimeCoefficient R W X b‖ ≤ M := by
    simpa only [M,n,Finset.prod_const,Finset.card_univ,one_pow,mul_one] using
      fullPrimeCoefficient_norm_bound R W X (fun _ => 1) (fun _ => zero_le_one) hW b
  have hcount : ((fullSquarefreePrimeSupport R W X e).card:ℝ) ≤
      C^n*(∏ i, X i)/L^n := by
    apply (fullSquarefreePrimeSupport_card_le_product R W X e).trans
    apply (Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
      (fun i _ => hcard W X L hL hX hlog i)).trans_eq
    simp only [Finset.prod_div_distrib,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,n]
  have hrow (b : Eisenstein) : ‖fullPrimeCoefficient R W X b‖ ≤ (M+1)^2 ∧
      ‖fullPrimeCoefficient R W X b‖^2 ≤ (M+1)^2 := by
    constructor
    · exact (hbound b).trans (by nlinarith)
    · exact (pow_le_pow_left₀ (_root_.norm_nonneg _) (hbound b) 2).trans (by nlinarith)
  constructor
  · calc
      _ ≤ ∑ b ∈ fullSquarefreePrimeSupport R W X e, (M+1)^2 :=
        Finset.sum_le_sum (fun b _ => (hrow b).1)
      _ = ((fullSquarefreePrimeSupport R W X e).card:ℝ)*(M+1)^2 := by simp
      _ ≤ (C^n*(∏ i, X i)/L^n)*(M+1)^2 :=
        mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ ∑ b ∈ fullSquarefreePrimeSupport R W X e, (M+1)^2 :=
        Finset.sum_le_sum (fun b _ => (hrow b).2)
      _ = ((fullSquarefreePrimeSupport R W X e).card:ℝ)*(M+1)^2 := by simp
      _ ≤ (C^n*(∏ i, X i)/L^n)*(M+1)^2 :=
        mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
      _ = _ := by ring

theorem fullPrimeCoefficient_power_scale_moments (hpnt : PrimaryPrimePNT)
    {R c : ℝ} (hR : 1 ≤ R) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Y : ℝ in Filter.atTop,
      ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ), (∀ i, Y^c ≤ X i) →
      (∀ i x, ‖W i x‖ ≤ 1) → ∀ e : Eisenstein,
      (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖) ≤
          K*(∏ i, X i)/(1+Real.log Y)^(Fintype.card ι) ∧
      (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2) ≤
          K*(∏ i, X i)/(1+Real.log Y)^(Fintype.card ι) := by
  obtain ⟨C,hC,hbound⟩ := fullPrimeCoefficient_sharp_moments (ι := ι) hpnt hR
  refine ⟨C/(c/2)^(Fintype.card ι),by positivity,?_⟩
  filter_upwards [(tendsto_rpow_atTop hc).eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_gt_atTop (0:ℝ)] with Y hYc hlogY hY
  intro W X hX hW e
  have hXi : ∀ i, 2 ≤ X i := fun i => hYc.trans (hX i)
  have hL : 0 < 1+Real.log Y := by linarith
  have hlog (i : ι) : (c/2)*(1+Real.log Y) ≤ Real.log (X i) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hY c) (hX i)
    rw [Real.log_rpow hY] at hh
    nlinarith
  have hh := hbound W X ((c/2)*(1+Real.log Y)) (by positivity) hXi hlog hW e
  have he : C*(∏ i, X i)/((c/2)*(1+Real.log Y))^(Fintype.card ι) =
      (C/(c/2)^(Fintype.card ι))*(∏ i, X i)/(1+Real.log Y)^(Fintype.card ι) := by
    rw [mul_pow]
    ring
  exact ⟨hh.1.trans_eq he,hh.2.trans_eq he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductModelMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal product model is bounded by the actual prime l¹ masses.
This preserves their density savings at the exceptional transition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem fullPrimeProductModel_l1_bound (R : ℝ)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (u : ℝ) :
    ‖fullPrimeProductModel R WA WB XA XB u‖ ≤
      (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1, ‖fullPrimeCoefficient R WA XA a‖)*
      (∑ b ∈ fullSquarefreePrimeSupport R WB XB 1, ‖fullPrimeCoefficient R WB XB b‖)*
      (cStar*((∏ i, XA i)*(∏ i, XB i))^(-1/6:ℝ)) := by
  let D := (∏ i, XA i)*(∏ i, XB i)
  have hD : 0 < D := mul_pos (Finset.prod_pos (fun i _ => hXA i))
    (Finset.prod_pos (fun i _ => hXB i))
  let F := fun a b : Eisenstein =>
    ((cStar:ℂ)*(idealMoebius (a*b):ℂ)^2*((norm (a*b)^(-1/6:ℝ):ℝ):ℂ))*normTwist u (a*b)
  have hF (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R WA XA 1)
      (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R WB XB 1) :
      ‖F a b‖ ≤ cStar*D^(-1/6:ℝ) := by
    have hn : D ≤ norm (a*b) := by
      rw [norm_mul_eq]
      exact mul_le_mul (fullPrimeProduct_norm_bounds R WA XA hXA hAlo hAhi
        (Finset.mem_filter.mp ha).1).1
        (fullPrimeProduct_norm_bounds R WB XB hXB hBlo hBhi
          (Finset.mem_filter.mp hb).1).1
        (Finset.prod_nonneg (fun i _ => (hXB i).le)) (norm_nonneg a)
    have hm : ‖(idealMoebius (a*b):ℂ)^2‖ ≤ 1 := by
      rw [norm_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (_root_.norm_nonneg _)
        (norm_idealMoebius_le_one (a*b)) 2
    simp only [F,norm_mul,norm_normTwist,mul_one,Complex.norm_real,
      Real.norm_of_nonneg cStar_pos.le,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg (a*b)) (-1/6:ℝ))]
    calc
      _ ≤ cStar*1*(norm (a*b))^(-1/6:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm cStar_pos.le)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hD hn (by norm_num)) cStar_pos.le
  convert fullPrimeProduct_weighted_bound R WA WB XA XB F hF using 1
  all_goals try with_reducible_and_instances rfl
  simp only [F,fullPrimeProductModel,mul_assoc]

theorem fullPrimeProductModel_density_bound
    {R A B Z MA MB : ℝ} (hA : 0 < A) (hB : 0 < B) (hZ : 0 < Z)
    (hMA : 0 ≤ MA) (_hMB : 0 ≤ MB)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hprodA : (∏ i, XA i) = A) (hprodB : (∏ i, XB i) = B)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hmA : (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1, ‖fullPrimeCoefficient R WA XA a‖) ≤ MA*A/Z^2)
    (hmB : (∑ b ∈ fullSquarefreePrimeSupport R WB XB 1, ‖fullPrimeCoefficient R WB XB b‖) ≤ MB*B/Z)
    (u : ℝ) :
    ‖fullPrimeProductModel R WA WB XA XB u‖ ≤
      (MA*MB*cStar)*A^(5/6:ℝ)*B^(5/6:ℝ)/Z^3 := by
  have hc := cStar_pos
  have hh := fullPrimeProductModel_l1_bound R WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi u
  rw [hprodA,hprodB] at hh
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul hmA hmB
    (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _)) (by positivity)) (by positivity)).trans_eq
  have he : (A*B)*(A*B)^(-1/6:ℝ) = A^(5/6:ℝ)*B^(5/6:ℝ) := by
    nth_rw 1 [← Real.rpow_one (A*B)]
    rw [← Real.rpow_add (mul_pos hA hB)]
    norm_num
    exact Real.mul_rpow hA.le hB.le
  calc
    (MA*A/Z^2)*(MB*B/Z)*(cStar*(A*B)^(-1/6:ℝ)) =
      (MA*MB*cStar)*((A*B)*(A*B)^(-1/6:ℝ))/Z^3 := by ring
    _ = _ := by rw [he]; ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubePoissonIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded dyadic sum is the literal noncube part of the lattice
Poisson identity. No frequency terms or coprimality conditions are dropped. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem noncubePoissonContribution_lattice (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ) (u : ℝ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {A : ℝ} (hA : 0 < A) :
    noncubePoissonContribution S β u V A =
      ∑' h : Eisenstein, if ∃ z : Eisenstein, z^3 = h then 0 else
        ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
          (β a*normTwist u a)*star (β b*normTwist u b)*
            (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h else 0 := by
  let G := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h else 0
  let F := fun h : Eisenstein => ∑ a ∈ S, ∑ b ∈ S,
    if ∃ z : Eisenstein, z^3 = h then 0 else G a b h
  have hG (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) :
      Summable (fun h : Eisenstein => if ∃ z : Eisenstein, z^3 = h then 0 else G a b h) := by
    by_cases hab : IsCoprime a b
    · have hs := ((summable_gramDualTerm (hS b hb) (hS a ha) V hV hV' hA).mul_left
        ((β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ))).indicator
          {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = h}
      convert hs using 1
      all_goals try with_reducible_and_instances rfl
      funext h
      by_cases hc : ∃ z : Eisenstein, z^3 = h
      · simp only [ite_eq_left hc, Set.indicator_of_notMem (show h ∉ {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = h} from fun hnot => hnot hc)]
      · simp only [ite_eq_right hc, Set.indicator_of_mem (show h ∈ {h : Eisenstein | ¬∃ z : Eisenstein, z^3 = h} from hc), G, ite_eq_left hab]
    · simp only [G,hab,ite_false, if_false,ite_self]
      exact summable_zero
  have hF : Summable F := summable_sum (fun a ha => summable_sum (fun b hb => hG a b ha hb))
  have hF0 : F 0 = 0 := by
    simp only [F, ite_eq_left (show ∃ z : Eisenstein, z^3 = 0 from ⟨0,by simp⟩), Finset.sum_const_zero]
  have hblocks := hasSum_frequencyDyad F hF hF0
  have heq (j : ℕ) : (∑ h ∈ frequencyDyad j, F h) =
      finitePoissonContribution S ((frequencyDyad j).filter (fun h => ¬∃ z : Eisenstein, z^3 = h))
        β u V A := by
    unfold finitePoissonContribution
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hc : ∃ z : Eisenstein, z^3 = h
    · simp only [F, ite_eq_left hc, ite_eq_right (not_not_intro hc), Finset.sum_const_zero]
    · simp only [F, ite_eq_right hc, ite_eq_left hc, G]
  simp_rw [heq] at hblocks
  change (∑' j : ℕ, finitePoissonContribution S
    ((frequencyDyad j).filter (fun h => ¬∃ z : Eisenstein, z^3 = h)) β u V A) = _
  rw [hblocks.tsum_eq]
  apply tsum_congr
  intro h
  by_cases hc : ∃ z : Eisenstein, z^3 = h
  · simp only [F, ite_eq_left hc, Finset.sum_const_zero]
  · simp only [F, ite_eq_right hc, G]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeDispersionPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cube/noncube splitting of the coprime portion of the variance.
No diagonal or shared-prime contribution is silently included here. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tsum_split_nonzero_cubes (F : Eisenstein → ℂ) (hF : Summable F) (h0 : F 0 = 0) :
    (∑' h : Eisenstein, F h) =
      (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then F h else 0) +
      (∑' h : Eisenstein, if ∃ j : Eisenstein, j^3 = h then 0 else F h) := by
  let P := fun h : Eisenstein => h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h)
  let Q := fun h : Eisenstein => ¬∃ j : Eisenstein, j^3 = h
  have hp := hF.indicator {h | P h}
  have hq := hF.indicator {h | Q h}
  have he (h : Eisenstein) : F h =
      {h | P h}.indicator F h+{h | Q h}.indicator F h := by
    by_cases hz : h = 0
    · subst h
      simp only [h0,Set.indicator_apply,ite_self,zero_add]
    · by_cases hc : ∃ j : Eisenstein, j^3 = h
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
    by_cases hc : ∃ j : Eisenstein, j^3 = h
    · rw [Set.indicator_of_notMem (show h ∉ {h | Q h} from fun hn => hn hc),ite_eq_left hc]
    · rw [Set.indicator_of_mem (show h ∈ {h | Q h} from hc),ite_eq_right hc]

theorem coprimeDispersionGram_split (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ a ≠ 1)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    coprimeDispersionGram S β u W A =
      cubePoissonContribution S β u W A+noncubePoissonContribution S β u W A := by
  rw [noncubePoissonContribution_lattice S (fun a ha => (hS a ha).1) β u W hW hW' hA]
  let F := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)*
      (if ∃ j : Eisenstein, j^3 = h then 0 else gramDualTerm b a W A h) else 0
  have hs (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) : Summable (F a b) := by
    by_cases hab : IsCoprime a b
    · have hf := ((summable_gramDualTerm (hS b hb).1 (hS a ha).1 W hW hW' hA).indicator
        {h : Eisenstein | ¬∃ j : Eisenstein, j^3 = h}).mul_left
          ((β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ))
      convert hf using 1
      all_goals try with_reducible_and_instances rfl
      funext h
      dsimp only [F]
      rw [ite_eq_left hab]
      congr 1
      by_cases hc : ∃ j : Eisenstein, j^3 = h
      · rw [ite_eq_left hc,Set.indicator_of_notMem
          (show h ∉ {h : Eisenstein | ¬∃ j : Eisenstein, j^3 = h} from fun hn => hn hc)]
      · rw [ite_eq_right hc,Set.indicator_of_mem
          (show h ∈ {h : Eisenstein | ¬∃ j : Eisenstein, j^3 = h} from hc)]
    · simp only [F,ite_eq_right hab]
      exact summable_zero
  have hswap : (∑' h : Eisenstein, if ∃ j : Eisenstein, j^3 = h then 0 else
      ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
        (β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)*
          gramDualTerm b a W A h else 0) = ∑ a ∈ S, ∑ b ∈ S, ∑' h, F a b h := by
    have he (h : Eisenstein) : (if ∃ j : Eisenstein, j^3 = h then 0 else
        ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
          (β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)*
            gramDualTerm b a W A h else 0) = ∑ a ∈ S, ∑ b ∈ S, F a b h := by
      by_cases hc : ∃ j : Eisenstein, j^3 = h
      · simp only [F,ite_eq_left hc,mul_zero,ite_self,Finset.sum_const_zero]
      · simp only [F,ite_eq_right hc]
    simp_rw [he]
    rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hs a b ha hb))]
    apply Finset.sum_congr rfl
    intro a ha
    exact Summable.tsum_finsetSum (fun b hb => hs a b ha hb)
  rw [hswap]
  unfold coprimeDispersionGram cubePoissonContribution
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,F]
    have hne : b ≠ a := by
      intro hba
      exact (hS a ha).2.2 (primary_unit_eq_one (isCoprime_self.mp (hba ▸ hab)) (hS a ha).1)
    rw [dispersion_pair_poisson (hS a ha).1 (hS b hb).1
      (hS a ha).2.1 (hS b hb).2.1 hab β u W hW hW' hA,
      tsum_split_nonzero_cubes _ (summable_gramDualTerm (hS b hb).1 (hS a ha).1 W hW hW' hA)
        (gramDualTerm_zero (hS b hb).1 (hS a ha).1 (hS b hb).2.1 (hS a ha).2.1 hab.symm hne W A),
      mul_add]
    simp only [star_mul,tsum_mul_left]
    ring
  · simp only [ite_eq_right hab,F,tsum_zero,add_zero]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed nonnegative majorant for the outer norm interval. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma dispersionCutoff_nonneg (R x : ℝ) : 0 ≤ dispersionCutoff R x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma dispersionCutoff_one {R x : ℝ} (hx : x ∈ Icc 1 R) :
    dispersionCutoff R x = 1 := by
  rw [dispersionCutoff,Real.smoothTransition.one_of_one_le (by linarith [hx.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hx.2]),one_mul]

lemma dispersionCutoff_low {R x : ℝ} (hx : x < 1/2) : dispersionCutoff R x = 0 := by
  rw [dispersionCutoff,Real.smoothTransition.zero_of_nonpos (by linarith),zero_mul]

lemma dispersionCutoff_high {R x : ℝ} (hx : R+1 < x) : dispersionCutoff R x = 0 := by
  rw [dispersionCutoff,Real.smoothTransition.zero_of_nonpos (show R+1-x ≤ 0 by linarith),mul_zero]

lemma dispersionCutoff_complex_smooth (R : ℝ) :
    ContDiff ℝ ∞ (fun x => (dispersionCutoff R x:ℂ)) := by
  unfold dispersionCutoff
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop)))

lemma dispersionCutoff_tsupport (R : ℝ) :
    tsupport (fun x => (dispersionCutoff R x:ℂ)) ⊆ Icc (1/2) (R+1) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (by change (dispersionCutoff R x:ℂ) = 0; rw [dispersionCutoff_low (lt_of_not_ge h)]; rfl)
  · by_contra h
    exact hx (by change (dispersionCutoff R x:ℂ) = 0; rw [dispersionCutoff_high (lt_of_not_ge h)]; rfl)

lemma dispersionCutoff_complex_compact (R : ℝ) :
    HasCompactSupport (fun x => (dispersionCutoff R x:ℂ)) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (dispersionCutoff_tsupport R)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWeightedMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SinglePrimeSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prime convolution with one coordinate equals its weighted prime set,
with the same exclusions and weights in the semiprime application. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma orderedConvolutionSupport_unit (S : Finset Eisenstein) :
    orderedConvolutionSupport (fun _ : Unit => S) = S := by
  ext n
  constructor
  · intro hn
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
    simpa only [Fintype.prod_unique] using Fintype.mem_piFinset.mp hf ()
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨fun _ : Unit => n,Fintype.mem_piFinset.mpr (fun _ => hn),?_⟩
    simp only [Fintype.prod_unique]

lemma fullSquarefreePrimeSupport_unit (R B : ℝ) (W : ℝ → ℂ) :
    fullSquarefreePrimeSupport R (fun _ : Unit => W) (fun _ => B) 1 =
      fullPrimeSupport R (fun _ : Unit => W) (fun _ => B) () := by
  rw [fullSquarefreePrimeSupport]
  change (orderedConvolutionSupport
    (fun _ : Unit => fullPrimeSupport R (fun _ : Unit => W) (fun _ => B) ())).filter
      (fun b => Squarefree b ∧ IsCoprime b 1) = _
  rw [orderedConvolutionSupport_unit]
  apply Finset.filter_eq_self.mpr
  intro p hp
  exact ⟨(fullPrimeSupport_prime R (fun _ : Unit => W) (fun _ => B) () p hp).2.squarefree,
    isCoprime_one_right⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SinglePrimeVariance
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uncorrected prime variance retains its diagonal. This is the
finite algebra and cube estimate needed at the three-prime transition. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem prime_variance_split (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (β : Eisenstein → ℂ) (u : ℝ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {A : ℝ} (hA : 0 < A) :
    smoothedDispersionVariance S β u V A =
      (∑ p ∈ S, dispersionAmplitude β u p*star (dispersionAmplitude β u p)*
        primaryCharacterGram p p V A) + coprimeDispersionGram S β u V A := by
  rw [smoothedDispersionVariance_gram S (fun p hp => (hS p hp).1) β u V hV hV' hA]
  unfold coprimeDispersionGram
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.add_sum_erase S _ hp]
  congr 1
  rw [← Finset.add_sum_erase S _ hp]
  have hself : ¬IsCoprime p p := fun h => (hS p hp).2.not_isUnit (isCoprime_self.mp h)
  simp only [hself,ite_false, if_false,zero_add]
  apply Finset.sum_congr rfl
  intro q hq
  rw [ite_eq_left (primaryPrimes_isCoprime (hS p hp)
    (hS q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq).symm)]

theorem primary_coprime_mass_bound (V : ℝ → ℂ) {A R M : ℝ}
    (hA : 0 < A) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hV : ∀ x, ‖V x‖ ≤ M) (hcut : ∀ x, R < x → V x = 0) (p : Eisenstein) :
    ‖∑' a : Eisenstein, if primary a ∧ IsCoprime p a then V (norm a/A) else 0‖ ≤
      18*R*A*M := by
  have he : (∑' a : Eisenstein, if primary a ∧ IsCoprime p a then V (norm a/A) else 0) =
      ∑ a ∈ primaryElementBall (R*A),
        if primary a ∧ IsCoprime p a then V (norm a/A) else 0 := by
    apply tsum_eq_sum
    intro a ha
    by_cases hp : primary a
    · have hn : R < norm a/A := by
        apply (lt_div_iff₀ hA).mpr
        exact lt_of_not_ge (fun h => ha (mem_primaryElementBall.mpr ⟨hp,h⟩))
      simp only [hcut _ hn,ite_self]
    · simp only [hp,false_and,ite_false, if_false]
  rw [he]
  calc
    _ ≤ ∑ a ∈ primaryElementBall (R*A),
        ‖if primary a ∧ IsCoprime p a then V (norm a/A) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ primaryElementBall (R*A), M := Finset.sum_le_sum (fun a _ => by
      split_ifs
      · exact hV _
      · simpa only [norm_zero] using hM)
    _ = ((primaryElementBall (R*A)).card:ℝ)*M := by simp
    _ ≤ (18*(R*A))*M := mul_le_mul_of_nonneg_right
      (primaryElementBall_card_le (mul_nonneg hR hA.le)) hM
    _ = _ := by ring

theorem prime_dispersion_diagonal_bound (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (β : Eisenstein → ℂ) (u : ℝ)
    (V : ℝ → ℂ) {A R M : ℝ} (hA : 0 < A) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hV : ∀ x, ‖V x‖ ≤ M) (hcut : ∀ x, R < x → V x = 0) :
    ‖∑ p ∈ S, dispersionAmplitude β u p*star (dispersionAmplitude β u p)*
        primaryCharacterGram p p V A‖ ≤ (18*R*M)*A*∑ p ∈ S, ‖β p‖^2 := by
  rw [dispersion_diagonal S (fun p hp => (hS p hp).1)
    (fun p hp => (hS p hp).2.squarefree) β u V A]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ S, ‖β p‖^2*(18*R*A*M) := Finset.sum_le_sum (fun p _ => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (primary_coprime_mass_bound V hA hR hM hV hcut p) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem coprimeCubeMainTerm_norm_bound (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hN : ∀ p ∈ S, B ≤ norm p) :
    ‖coprimeCubeMainTerm S β u V A‖ ≤
      (A^(2/3:ℝ)*B^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖)*
        (∑ p ∈ S, ‖β p‖)^2 := by
  unfold coprimeCubeMainTerm
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ S, ∑ q ∈ S,
        ‖β p‖*‖β q‖*(A^(2/3:ℝ)*B^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖) := by
      apply Finset.sum_le_sum
      intro p hp
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      split_ifs
      · have hrad : 0 ≤ A^(2/3:ℝ)*(norm (q*p))^(-(1/6:ℝ))/9 :=
          div_nonneg (mul_nonneg (Real.rpow_nonneg hA _)
            (Real.rpow_nonneg (norm_nonneg _) _)) (by norm_num)
        simp only [norm_mul,norm_star,norm_normTwist,mul_one,Complex.norm_real,
          Real.norm_of_nonneg hrad]
        have hh := (cube_pair_norm_bounds hB (hN p hp) (hN q hq)).2
        calc
          _ ≤ ‖β p‖*‖β q‖*(A^(2/3:ℝ)*B^(-(1/3:ℝ))/9)*‖cubeProfileIntegral V‖ := by
            gcongr
          _ = _ := by ring
      · simp only [norm_zero]; positivity
    _ = _ := by
      simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring

lemma cube_transition_scale {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B^2) :
    A/B ≤ A^(2/3:ℝ)*B^(-(1/3:ℝ)) := by
  have hh := Real.rpow_le_rpow hA.le hAB (show (0:ℝ) ≤ 1/3 by norm_num)
  rw [← Real.rpow_natCast B 2,← Real.rpow_mul hB.le] at hh
  have ha : A = A^(2/3:ℝ)*A^(1/3:ℝ) := by
    rw [← Real.rpow_add hA]; norm_num
  calc
    A/B = A^(2/3:ℝ)*A^(1/3:ℝ)/B := by rw [← ha]
    _ ≤ A^(2/3:ℝ)*B^(2/3:ℝ)/B := by gcongr; norm_num at hh ⊢; exact hh
    _ = _ := by rw [div_eq_mul_inv,← Real.rpow_neg_one B,
      mul_assoc,← Real.rpow_add hB]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SinglePrimeTransition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cube bound at the transition keeps the coefficient l¹ mass,
and the full prime variance keeps its diagonal l² mass. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem prime_variance_transition_bound (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hVM : ∀ x, ‖V x‖ ≤ M) (hcut : ∀ x, R < x → V x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein),
      (∀ p ∈ S, primaryPrime p) → ∀ (β : Eisenstein → ℂ) (u A B : ℝ),
      0 < A → 0 < B → A ≤ B^2 → (∀ p ∈ S, B ≤ norm p) →
      (∀ p ∈ S, ∀ q ∈ S,
        (∑ r ∈ primaryPrimeFactors p ∪ primaryPrimeFactors q, 1/norm r) ≤ 4) →
      ‖smoothedDispersionVariance S β u V A‖ ≤
        K*A*(∑ p ∈ S, ‖β p‖^2) +
        K*A^(2/3:ℝ)*B^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2 +
        ‖noncubePoissonContribution S β u V A‖ := by
  obtain ⟨C,D,hC,hD,hcube⟩ := cubePoissonContribution_uniform_error V hV hV'
  let K₀ := C+4*D+‖cubeProfileIntegral V‖
  let K := K₀+18*R*M+1
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hK : 0 < K := by dsimp [K,K₀]; positivity
  refine ⟨K,hK,?_⟩
  intro S hS β u A B hA hB hAB hN hrough
  let t := A^(2/3:ℝ)*B^(-(1/3:ℝ))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hdiag := prime_dispersion_diagonal_bound S hS β u V hA hR hM hVM hcut
  have hc := hcube S (fun p hp => ⟨(hS p hp).1,(hS p hp).2.squarefree⟩)
    A B 4 hA hB (by norm_num) (hAB.trans (by nlinarith [sq_nonneg B])) hN hrough β u
  have hm := coprimeCubeMainTerm_norm_bound S β u V hA.le hB hN
  have hscale := cube_transition_scale hA hB hAB
  have hfirst : C*A/(27*B) ≤ C*t := by
    calc
      _ = C*(A/B)/27 := by ring
      _ ≤ C*(A/B) := div_le_self (by positivity) (by norm_num)
      _ ≤ C*t := mul_le_mul_of_nonneg_left hscale hC.le
  have hcoef : C*A/(27*B)+D*t*4/9+t/9*‖cubeProfileIntegral V‖ ≤ K₀*t := by
    dsimp [K₀]
    nlinarith [mul_nonneg hD.le ht,mul_nonneg ht (_root_.norm_nonneg (cubeProfileIntegral V))]
  have hcubebound : ‖cubePoissonContribution S β u V A‖ ≤
      K₀*t*(∑ p ∈ S, ‖β p‖)^2 := by
    apply (norm_le_norm_sub_add (cubePoissonContribution S β u V A)
      (coprimeCubeMainTerm S β u V A)).trans
    apply ((add_le_add hc hm).trans_eq ?_).trans
      (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
    dsimp [t]
    ring
  have hKS : K₀ ≤ K := by
    have hh : 0 ≤ 18*R*M := by positivity
    dsimp [K]
    linarith
  have hKD : 18*R*M ≤ K := by dsimp [K]; linarith
  have hmain (p : Eisenstein) (hp : p ∈ S) : primary p ∧ Squarefree p ∧ p ≠ 1 :=
    ⟨(hS p hp).1,(hS p hp).2.squarefree,fun h => (hS p hp).2.not_isUnit (h ▸ isUnit_one)⟩
  rw [prime_variance_split S hS β u V hV hV' hA,
    coprimeDispersionGram_split S hmain β u V hV hV' hA]
  apply (norm_add_le _ _).trans
  apply (add_le_add hdiag ((norm_add_le _ _).trans
    (add_le_add hcubebound (le_refl _)))).trans
  dsimp [t]
  have he : 0 ≤ ∑ p ∈ S, ‖β p‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKD hA.le) he
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKS ht) (sq_nonneg (∑ p ∈ S, ‖β p‖))
  dsimp [t] at hb
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SinglePrimeTransitionInput
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime transition variance from the precise published noncube
inputs. No transition or dispersion theorem of the new paper is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem single_prime_transition_variance {γ : Type*}
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C R M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hVM : ∀ x, ‖V x‖ ≤ M)
    (hcut : ∀ x, R < x → V x = 0)
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (k U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ), T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
      let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
      ‖smoothedDispersionVariance S β u V A‖ ≤ K*(
        A*(∑ p ∈ S, ‖β p‖^2) +
        A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2 +
        A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by
  obtain ⟨η,σ,hη,hη1,hσ,hmain⟩ := noncube_poisson_total_saving
    (γ := γ) (ι := Unit) (c := 1/2) (R := 2) hSW hpub hHuxley hperiod
    hMV hC (by norm_num) (by norm_num) (by norm_num) hGI hGQ V hV hV' k U
  obtain ⟨Kn,T₀,hKn,hn⟩ := hmain L (fun r _ => W r) hL
    (uniformLogWeights_prime_coordinates L W hL hW) (fun r _ => hlo r) (fun r _ => hhi r)
  obtain ⟨Kc,hKc,hc⟩ := prime_variance_transition_bound V hV hV' hR hM hVM hcut
  refine ⟨η,Kc+Kn,T₀,hη,hη1,by positivity,?_⟩
  intro r A u hT hrough hAlo hAhi hu
  dsimp only
  let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
  let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p := by
    dsimp only [S] at hp
    rw [fullSquarefreePrimeSupport_unit] at hp
    exact fullPrimeSupport_prime 2 (fun _ : Unit => W r) (fun _ => L r) () p hp
  have hN (p : Eisenstein) (hp : p ∈ S) : L r ≤ norm p := by
    have hh := (fullPrimeProduct_norm_bounds 2 (fun _ : Unit => W r) (fun _ => L r)
      (fun _ => hB) (fun _ => hlo r) (fun _ => hhi r) (Finset.mem_filter.mp hp).1).1
    simpa only [Fintype.prod_unique] using hh
  have hpq (p : Eisenstein) (hp : p ∈ S) (q : Eisenstein) (hq : q ∈ S) :
      (∑ t ∈ primaryPrimeFactors p ∪ primaryPrimeFactors q, 1/norm t) ≤ 4 := by
    have hh := fullPrime_pair_reciprocal_sum_le (D := L r/2) (by positivity)
      (fun _ : Unit => W r) (fun _ => L r) (fun _ => hB)
      (fun _ => hlo r) (fun _ => hhi r) (fun _ => by linarith) 1 hp hq
    norm_num only [Fintype.card_unique,Nat.cast_one,mul_one] at hh
    apply hh.trans
    apply (div_le_iff₀ (show 0 < L r/2 by positivity)).mpr
    nlinarith [hL r]
  have hh := hc S hS β u A (L r) hA hB hAhi hN hpq
  have hnon := hn r (fun _ => L r) A 1 u hT (by simp) (fun _ => hrough)
    hAlo hAhi one_ne_zero
    (by simpa only [norm_one_eq] using Real.one_le_rpow (hL r) hσ.le) hu
  change ‖noncubePoissonContribution S β u V A‖ ≤ _ at hnon
  change ‖smoothedDispersionVariance S β u V A‖ ≤ (Kc+Kn)*(
    A*(∑ p ∈ S, ‖β p‖^2) +
    A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2 +
    A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k)
  apply (hh.trans (add_le_add (le_refl _) hnon)).trans
  have he : 0 ≤ A*(∑ p ∈ S, ‖β p‖^2) :=
    mul_nonneg hA.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hm : 0 ≤ A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2 := by positivity
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hq : 0 ≤ A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by positivity
  calc
    _ = Kc*(A*(∑ p ∈ S, ‖β p‖^2)) +
        Kc*(A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2) +
        Kn*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ (Kc+Kn)*(A*(∑ p ∈ S, ‖β p‖^2)) +
        (Kc+Kn)*(A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2) +
        (Kc+Kn)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (by linarith) he)
        (mul_le_mul_of_nonneg_right (by linarith) hm))
        (mul_le_mul_of_nonneg_right (by linarith) hq)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTransitionDensity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime density supplies the logarithms in the uncorrected transition
variance; the diagonal is retained separately. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment

theorem single_prime_transition_log_variance {γ : Type*} (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C R M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hVM : ∀ x, ‖V x‖ ≤ M)
    (hcut : ∀ x, R < x → V x = 0)
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ), T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
      let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
      ‖smoothedDispersionVariance S β u V A‖ ≤ K*(
        A*L r/(1+Real.log (L r)) +
        A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2) := by
  obtain ⟨η,K,T,hη,hη1,hK,hvar⟩ := single_prime_transition_variance hSW hpub hHuxley
    hperiod hMV hC hGI hGQ V hV hV' hR hM hVM hcut L W hL hW hlo hhi 2 U
  obtain ⟨D,hD,hmoment⟩ := fullPrimeCoefficient_sharp_moments (ι := Unit) hpnt
    (R := 2) (by norm_num)
  let E := 2*D
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨η,K*(E+E^2+1),max T (max 2 (Real.exp 1)),hη,hη1,by positivity,?_⟩
  intro r A u hT hrough hAlo hAhi hu
  dsimp only
  let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
  let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have h2 : 2 ≤ L r := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hexp : Real.exp 1 ≤ L r := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hlog : 1 ≤ Real.log (L r) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have hz : 0 < 1+Real.log (L r) := by linarith
  have hm := hmoment (fun _ : Unit => W r) (fun _ => L r) ((1+Real.log (L r))/2)
    (by positivity) (fun _ => h2) (fun _ => by linarith) (fun _ => hW1 r) 1
  have heq : D*(∏ _i : Unit, L r)/((1+Real.log (L r))/2)^(Fintype.card Unit) =
      E*L r/(1+Real.log (L r)) := by
    simp only [Fintype.prod_unique,Fintype.card_unique,pow_one]
    dsimp [E]
    field_simp
  rw [heq] at hm
  have hv := hvar r A u ((le_max_left _ _).trans hT) hrough hAlo hAhi hu
  change ‖smoothedDispersionVariance S β u V A‖ ≤ _ at hv ⊢
  have hm₁ : (∑ p ∈ S, ‖β p‖) ≤ E*L r/(1+Real.log (L r)) := hm.1
  have hm₂ : (∑ p ∈ S, ‖β p‖^2) ≤ E*L r/(1+Real.log (L r)) := hm.2
  have hm₁sq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _)) hm₁ 2
  have hpower : (L r)^(-(1/3:ℝ))*(L r)^2 = (L r)^(5/3:ℝ) := by
    rw [← Real.rpow_natCast (L r) 2,← Real.rpow_add hB]
    norm_num
  have hnorm : A*(E*L r/(1+Real.log (L r)))+
      A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(E*L r/(1+Real.log (L r)))^2+
      A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2 =
      E*(A*L r/(1+Real.log (L r)))+
      (E^2+1)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2) := by
    rw [div_pow,mul_pow,← hpower]
    ring
  apply hv.trans
  calc
    _ ≤ K*(A*(E*L r/(1+Real.log (L r)))+
        A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(E*L r/(1+Real.log (L r)))^2+
        A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2) := by
      gcongr
    _ = K*(E*(A*L r/(1+Real.log (L r)))+
        (E^2+1)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2)) := by rw [hnorm]
    _ ≤ K*(E+E^2+1)*(A*L r/(1+Real.log (L r))+
        A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2) := by
      have hx : 0 ≤ A*L r/(1+Real.log (L r)) := by positivity
      have hy : 0 ≤ A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^2 := by positivity
      nlinarith [mul_nonneg (by positivity : 0 ≤ E^2+1) hx,mul_nonneg hE.le hy]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTransitionScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The diagonal and cube terms both give the required three-prime
logarithmic saving after Cauchy--Schwarz. -/
noncomputable section
namespace CubicFirstMoment

lemma transition_diagonal_scale {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hAB : A ≤ B^2) : A^2*B ≤ A^(5/3:ℝ)*B^(5/3:ℝ) := by
  have hh := Real.rpow_le_rpow hA.le hAB (show (0:ℝ) ≤ 1/3 by norm_num)
  rw [← Real.rpow_natCast B 2,← Real.rpow_mul hB.le] at hh
  norm_num at hh
  have ha : A^2 = A^(5/3:ℝ)*A^(1/3:ℝ) := by
    rw [← Real.rpow_add hA]; norm_num [Real.rpow_two]
  have hb : B^(5/3:ℝ) = B^(2/3:ℝ)*B := by
    calc
      _ = B^((2/3:ℝ)+1) := by norm_num
      _ = B^(2/3:ℝ)*B^((1:ℝ)) := Real.rpow_add hB _ _
      _ = _ := by rw [Real.rpow_one]
  rw [ha,hb,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hA.le _)
  exact mul_le_mul_of_nonneg_right (by simpa using hh) hB.le

lemma prime_transition_cauchy_scale {A B Z K M n : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hZ : 1 ≤ Z) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hAB : A ≤ B^2)
    (hn : n^2 ≤ (M*A/Z^2)*(K*(A*B/Z+A^(2/3:ℝ)*B^(5/3:ℝ)/Z^2))) :
    n ≤ Real.sqrt (2*M*K)*A^(5/6:ℝ)*B^(5/6:ℝ)/Z^(3/2:ℝ) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hdiag := transition_diagonal_scale hA hB hAB
  have hpowA : A*A^(2/3:ℝ) = A^(5/3:ℝ) := by
    conv_lhs => arg 1; rw [← Real.rpow_one A]
    rw [← Real.rpow_add hA]; norm_num
  have hZ34 : Z^3 ≤ Z^4 := by nlinarith [pow_nonneg hZp.le 3]
  have hsplit : (M*A/Z^2)*(K*(A*B/Z+A^(2/3:ℝ)*B^(5/3:ℝ)/Z^2)) =
      (M*K)*(A^2*B)/Z^3+(M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^4 := by
    rw [← hpowA]
    field_simp
  have hs : n^2 ≤ (2*M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^3 := by
    apply hn.trans
    rw [hsplit]
    calc
      _ ≤ (M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^3+
          (M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^3 := by
        apply add_le_add
        · gcongr
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity) hZ34
      _ = _ := by ring
  have hsquare : (Real.sqrt (2*M*K)*A^(5/6:ℝ)*B^(5/6:ℝ)/Z^(3/2:ℝ))^2 =
      (2*M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^3 := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity),
      ← Real.rpow_mul_natCast hA.le,← Real.rpow_mul_natCast hB.le,
      ← Real.rpow_mul_natCast hZp.le]
    norm_num [Real.rpow_natCast]
    ring
  have hnonneg : 0 ≤ Real.sqrt (2*M*K)*A^(5/6:ℝ)*B^(5/6:ℝ)/Z^(3/2:ℝ) := by positivity
  rw [← hsquare] at hs
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTransitionBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uncorrected one-prime/two-prime transition estimate. The outer
energy assumption can be filled by the actual two-coordinate PNT count. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem single_prime_transition_bilinear {γ : Type*} (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C Q M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hQ : 1 ≤ Q) (hM : 0 ≤ M)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ) (P : Finset Eisenstein) (α : Eisenstein → ℂ),
      T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      (∀ a ∈ P, primary a ∧ norm a/A ∈ Set.Icc 1 Q) →
      (∑ a ∈ P, ‖α a‖^2) ≤ M*A/(1+Real.log (L r))^2 →
      let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
      let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
      ‖∑ a ∈ P, ∑ p ∈ S, α a*β p*gauss (a*p)*normTwist u (a*p)‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
  let V := fun x => (dispersionCutoff Q x:ℂ)
  have hVM (x : ℝ) : ‖V x‖ ≤ 1 := by
    dsimp [V]
    rw [Complex.norm_real,Real.norm_of_nonneg (dispersionCutoff_nonneg Q x)]
    exact (mul_le_mul (Real.smoothTransition.le_one _)
      (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul 1)
  obtain ⟨η,K,T,hη,hη1,hK,hvar⟩ := single_prime_transition_log_variance hpnt hSW hpub
    hHuxley hperiod hMV hC hGI hGQ V (dispersionCutoff_complex_compact Q)
    (dispersionCutoff_complex_smooth Q) (by linarith : 0 ≤ Q+1) (by norm_num)
    hVM (fun x hx => by simp only [V,dispersionCutoff_high hx,Complex.ofReal_zero])
    L W hL hW hlo hhi hW1 U
  refine ⟨η,Real.sqrt (2*M*K)+1,T,hη,hη1,by positivity,?_⟩
  intro r A u P α hT hrough hAlo hAhi hu hP henergy
  dsimp only
  let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
  let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hZ : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hS (p : Eisenstein) (hp : p ∈ S) : primary p :=
    (fullSquarefreePrimeSupport_primary 2 (fun _ : Unit => W r) (fun _ => L r) 1 hp).1
  have hc := bilinear_full_variance_bound_sq P S α β u (fun a ha => (hP a ha).1) hS
    (dispersionCutoff Q) (dispersionCutoff_nonneg Q) (dispersionCutoff_complex_compact Q)
    (dispersionCutoff_complex_smooth Q) hA (fun a ha => by rw [dispersionCutoff_one (hP a ha).2])
  have hv := hvar r A u hT hrough hAlo hAhi hu
  change ‖smoothedDispersionVariance S β u V A‖ ≤ _ at hv
  have hb := hc.trans (mul_le_mul henergy hv (_root_.norm_nonneg _) (by positivity))
  have hs := prime_transition_cauchy_scale hA hB hZ hK.le hM hAhi hb
  apply hs.trans
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  gcongr
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TripleTransitionBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Insert the actual two-prime coefficient in the transition bound.
Its outer energy is proved from the PNT, not assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem two_prime_transition_bilinear {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hc : 0 < c)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
      T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      (∏ i, XA i) = A → (∀ i, (L r)^c ≤ XA i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) →
      let P := fullSquarefreePrimeSupport 2 WA XA 1
      let α := fullPrimeCoefficient 2 WA XA
      let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
      let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
      ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist u (a*b)‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
  obtain ⟨M,hM,hmass⟩ := fullPrimeCoefficient_power_scale_moments (ι := ι) hpnt
    (R := 2) (by norm_num) hc
  obtain ⟨Tm,hmass⟩ := eventually_atTop.mp hmass
  obtain ⟨η,K,T,hη,hη1,hK,hbound⟩ := single_prime_transition_bilinear hpnt hSW hpub
    hHuxley hperiod hMV hC (by norm_num : (1:ℝ) ≤ 4) hM.le hGI hGQ
    L W hL hW hlo hhi hW1 U
  refine ⟨η,K,max T Tm,hη,hη1,hK,?_⟩
  intro r A u WA XA hT hrough hAlo hAhi hu hprod hXA hAlow hAhigh hWA
  dsimp only
  let P := fullSquarefreePrimeSupport 2 WA XA 1
  let α := fullPrimeCoefficient 2 WA XA
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hXi (i : ι) : 0 < XA i := (Real.rpow_pos_of_pos hB c).trans_le (hXA i)
  have hP (a : Eisenstein) (ha : a ∈ P) : primary a ∧ norm a/A ∈ Set.Icc 1 4 := by
    have hp := fullSquarefreePrimeSupport_primary 2 WA XA 1 ha
    have hn := fullPrimeProduct_norm_bounds 2 WA XA hXi hAlow hAhigh
      (Finset.mem_filter.mp ha).1
    rw [hprod,hcard] at hn
    refine ⟨hp.1,(le_div_iff₀ hA).mpr (by simpa using hn.1),?_⟩
    apply (div_le_iff₀ hA).mpr
    norm_num at hn
    exact hn.2
  have hm := (hmass (L r) ((le_max_right _ _).trans hT) WA XA hXA hWA 1).2
  rw [hprod,hcard] at hm
  exact hbound r A u P α ((le_max_left _ _).trans hT) hrough hAlo hAhi hu hP hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TripleTransitionCentered
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-prime/one-prime centered polynomial at the transition.
Both coefficient masses are derived from prime counting. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem two_prime_transition_centered_oai {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hc : 0 < c)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
      T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      (∏ i, XA i) = A → (∀ i, (L r)^c ≤ XA i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) →
      ‖centeredProductPolynomial (fullSquarefreePrimeSupport 2 WA XA 1)
        (fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1)
        (fullPrimeCoefficient 2 WA XA)
        (fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)) 0 u‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
  obtain ⟨η,Kg,Tg,hη,hη1,hKg,hgauss⟩ := two_prime_transition_bilinear hcard hpnt
    hSW hpub hHuxley hperiod hMV hC hc hGI hGQ L W hL hW hlo hhi hW1 U
  obtain ⟨MA,hMA,hmA⟩ := fullPrimeCoefficient_power_scale_moments (ι := ι) hpnt
    (R := 2) (by norm_num) hc
  obtain ⟨TA,hmA⟩ := eventually_atTop.mp hmA
  obtain ⟨MB,hMB,hmB⟩ := fullPrimeCoefficient_power_scale_moments (ι := Unit) hpnt
    (R := 2) (by norm_num) (by norm_num : (0:ℝ) < 1)
  obtain ⟨TB,hmB⟩ := eventually_atTop.mp hmB
  let Km := MA*MB*cStar
  have hKm : 0 < Km := mul_pos (mul_pos hMA hMB) cStar_pos
  refine ⟨η,Kg+Km,max Tg (max TA TB),hη,hη1,by positivity,?_⟩
  intro r A u WA XA hT hrough hAlo hAhi hu hprod hXA hAlow hAhigh hWA
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hXi (i : ι) : 0 < XA i := (Real.rpow_pos_of_pos hB c).trans_le (hXA i)
  have hma := (hmA (L r) ((le_max_left _ _).trans ((le_max_right _ _).trans hT))
    WA XA hXA hWA 1).1
  rw [hprod,hcard] at hma
  have hmb := (hmB (L r) ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
    (fun _ : Unit => W r) (fun _ => L r) (by intro _; rw [Real.rpow_one])
    (fun _ => hW1 r) 1).1
  simp only [Fintype.card_unique,Fintype.prod_unique,pow_one] at hmb
  have hm := fullPrimeProductModel_density_bound hA hB hz hMA.le hMB.le WA
    (fun _ : Unit => W r) XA (fun _ => L r) hXi (fun _ => hB) hprod (by simp)
    hAlow hAhigh (fun _ => hlo r) (fun _ => hhi r) hma hmb u
  have hg := hgauss r A u WA XA ((le_max_left _ _).trans hT) hrough hAlo hAhi hu
    hprod hXA hAlow hAhigh hWA
  change ‖fullPrimeProductGauss 2 WA (fun _ : Unit => W r) XA (fun _ => L r) u‖ ≤ _ at hg
  have hdenom : (1+Real.log (L r))^(3/2:ℝ) ≤ (1+Real.log (L r))^3 := by
    rw [← Real.rpow_natCast (1+Real.log (L r)) 3]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.log_nonneg (hL r)]) (by norm_num)
  have hm' : ‖fullPrimeProductModel 2 WA (fun _ : Unit => W r) XA (fun _ => L r) u‖ ≤
      Km*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) :=
    hm.trans (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hz _) hdenom)
  rw [fullPrimeProduct_centered]
  apply (norm_sub_le _ _).trans
  exact (add_le_add hg hm').trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CubicFirstMoment.two_prime_transition_centered_oai.{u_1, u_2} := @OAI.CubicFirstMoment.two_prime_transition_centered_oai.{u_1, u_2}
