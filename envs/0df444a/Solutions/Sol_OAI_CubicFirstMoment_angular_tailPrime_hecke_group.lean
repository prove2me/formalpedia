-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_tailPrime_hecke_group
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:17:27.399319+00:00
-- url     : https://prove2.me/submissions/6b33dd0d-1fb9-4919-a248-63500db46015

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022
import Theorems.Thm_OAI_CubicFirstMoment_angular_height_poisson_dyadic_saving
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic properties of the actual compactly supported smooth norm
weights. Passing to logarithmic coordinates realizes every vertical
Mellin line as a Schwartz Fourier transform. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

lemma mellinVerticalSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ t : ℝ) :
    mellinVerticalSchwartz W hW hpos hsm σ t = mellin W (σ + (t : ℂ)*Complex.I) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rfl

theorem smooth_mellin_vertical_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin W) σ := by
  change Integrable (fun t : ℝ => mellin W (σ + (t : ℂ)*Complex.I))
  have hi : Integrable (mellinVerticalSchwartz W hW hpos hsm σ) :=
    (mellinVerticalSchwartz W hW hpos hsm σ).integrable
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  exact (mellinVerticalSchwartz_apply W hW hpos hsm σ t).symm

/-- The Mellin inversion used for a single norm weight, with convergence
and the vertical integral discharged from its actual smooth support. -/
theorem smooth_mellin_inversion (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) : mellinInv σ (mellin W) x = W x :=
  mellinInv_mellin_eq σ W hx (smooth_mellin_convergent W hW hpos hsm.continuous σ)
    (smooth_mellin_vertical_integrable W hW hpos hsm σ) hsm.continuous.continuousAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute sum-integral interchange for the full norm Dirichlet series
in Mellin inversion. No smooth-duality formula is an input. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

/-- The complete smoothed series has the exact Mellin representation on
any line of absolute convergence of its norm Dirichlet series. -/
theorem smooth_mellin_series {ι : Type*} [Countable ι]
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    (habs : Summable (fun i => ‖a i‖*(N i)^(-σ)))
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' i, a i*W (N i/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
        normDirichletSeries a N (σ+(τ:ℂ)*Complex.I) := by
  let s (τ : ℝ) : ℂ := σ+(τ:ℂ)*Complex.I
  let F (i : ι) (τ : ℝ) : ℂ :=
    (a i*(N i:ℂ)^(-s τ))*((Z:ℂ)^(s τ)*mellin W (s τ))
  have hsre (τ : ℝ) : (s τ).re = σ := by simp [s]
  have hsnre (τ : ℝ) : (-s τ).re = -σ := by simp [hsre]
  have hnorm (i : ι) (τ : ℝ) : ‖F i τ‖ =
      (‖a i‖*(N i)^(-σ))*Z^σ*‖mellin W (s τ)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i),
      Complex.norm_cpow_eq_rpow_re_of_pos hZ,hsre,hsnre]
    ring
  have hm : Integrable (fun τ => mellin W (s τ)) :=
    smooth_mellin_vertical_integrable W hW hpos hsm σ
  have hFi (i : ι) : Integrable (F i) := by
    have hn0 : (N i:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN i).ne'
    have hz0 : (Z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
    have : NeZero (N i:ℂ) := ⟨hn0⟩
    have : NeZero (Z:ℂ) := ⟨hz0⟩
    have hs : Continuous s := by dsimp [s]; fun_prop
    have hc : Continuous (F i) :=
      (continuous_const.mul ((differentiable_const_cpow_of_neZero _).continuous.comp hs.neg)).mul
        (((differentiable_const_cpow_of_neZero _).continuous.comp hs).mul
          ((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp hs))
    exact (hm.norm.const_mul ((‖a i‖*(N i)^(-σ))*Z^σ)).mono'
      hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun τ => (hnorm i τ).le))
  have hsum : Summable (fun i => ∫ τ : ℝ, ‖F i τ‖) := by
    have he (i : ι) : (∫ τ : ℝ, ‖F i τ‖) =
        (‖a i‖*(N i)^(-σ))*(Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖)) := by
      simp_rw [hnorm]
      rw [integral_const_mul]
      ring
    simpa only [he] using habs.mul_right (Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖))
  have hi := integral_tsum_of_summable_integral_norm hFi hsum
  have hsingle (i : ι) : a i*W (N i/Z) =
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := by
    rw [← smooth_mellin_inversion W hW hpos hsm σ (div_pos (hN i) hZ),mellinInv]
    simp only [RCLike.real_smul_eq_coe_mul]
    rw [← mul_assoc,mul_comm (a i),mul_assoc,← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with τ
    rw [mellin_scale_cpow (hN i) hZ]
    dsimp [F,s]
    ring
  calc
    _ = ∑' i, ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := tsum_congr hsingle
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∑' i, ∫ τ : ℝ, F i τ) := tsum_mul_left
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, ∑' i, F i τ) := by rw [hi]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with τ
      simp only [F,normDirichletSeries]
      rw [tsum_mul_right]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMellinProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Mellin separation of a finite product-norm weight. This is the
exact analytic bridge used after the smooth short-convolution partition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem smooth_mellin_finite {κ : Type*} [Fintype κ]
    (a : κ → ℂ) (N : κ → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    (∑ i, a i*W (N i/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        (∑ i, a i*(N i:ℂ)^(-(σ+(τ:ℂ)*Complex.I))) := by
  simpa only [normDirichletSeries,tsum_fintype] using
    smooth_mellin_series a N hN W hW hpos hsm σ (hasSum_fintype _).summable hZ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DualPolynomialScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact `sqrt(Z/J)` normalization of a retained dual norm block.
The normalized coefficients are independent of the character conductor. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma positive_cpow_phase {x : ℝ} (hx : 0 < x) (σ u : ℝ) :
    (x:ℂ)^((σ:ℂ)+(u:ℂ)*Complex.I) = (x^σ:ℝ)*mellinPhase u x := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp]
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSmoothDual
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From the ordinary analytic properties of a primitive Hecke series
to a truncated smooth dual sum. The smooth-duality conclusion follows from the contour shift. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma mellinPhase_eq_cpow {x : ℝ} (hx : 0 < x) (t : ℝ) :
    mellinPhase t x = (x:ℂ)^((t:ℂ)*Complex.I) := by
  simpa only [Complex.ofReal_zero,zero_add,Real.rpow_zero,Complex.ofReal_one,one_mul]
    using (positive_cpow_phase hx 0 t).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and Mellin weights for actual finite smooth short sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellinWeight_norm (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (τ : ℝ) :
    ‖zeroLineMellinWeight V Z τ‖ =
      (1/(2*Real.pi))*‖mellin V ((τ:ℂ)*Complex.I)‖ := by
  rw [zeroLineMellinWeight,norm_mul,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,sub_self,Real.rpow_zero,mul_one,
    Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : (0:ℝ) < 1/(2*Real.pi))]

theorem zeroLineMellinWeight_integrable (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    Integrable (zeroLineMellinWeight V Z) := by
  have hm : Integrable (fun τ : ℝ => mellin V ((τ:ℂ)*Complex.I)) := by
    have h := smooth_mellin_vertical_integrable V hV hpos hsm 0
    change Integrable (fun τ : ℝ => mellin V ((0:ℂ)+(τ:ℂ)*Complex.I)) at h
    simpa only [zero_add] using h
  have hz : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hZ.ne'⟩
  have hp : Continuous (fun τ : ℝ => (Z:ℂ)^((τ:ℂ)*Complex.I)) :=
    (differentiable_const_cpow_of_neZero _).continuous.comp (by fun_prop)
  have ha : AEStronglyMeasurable (zeroLineMellinWeight V Z) :=
    ((hm.aestronglyMeasurable.const_mul _).mul hp.aestronglyMeasurable)
  exact (hm.norm.const_mul (1/(2*Real.pi))).mono' ha
    (Filter.Eventually.of_forall (fun τ => (zeroLineMellinWeight_norm V hZ τ).le))

lemma zeroLineMellinWeight_mass (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) :
    (∫ τ : ℝ, ‖zeroLineMellinWeight V Z τ‖) = zeroLineMellinMass V := by
  simp_rw [zeroLineMellinWeight_norm V hZ]
  exact integral_const_mul _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinHeightTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rapid Mellin truncation with an explicit integrable moment. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem zeroLineMellinWeight_moment_integrable (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V)
    {Z : ℝ} (hZ : 0 < Z) (A : ℕ) :
    Integrable (fun t : ℝ => |t|^A*‖zeroLineMellinWeight V Z t‖) := by
  let F := mellinVerticalSchwartz V hV hpos hsm 0
  have h := (F.integrable_pow_mul volume A).const_mul (1/(2*Real.pi))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [zeroLineMellinWeight_norm V hZ]
  dsimp [F]
  rw [mellinVerticalSchwartz_apply]
  simp only [Complex.ofReal_zero,zero_add]
  ring

lemma zeroLineMellinWeight_moment (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (A : ℕ) :
    (∫ t : ℝ, |t|^A*‖zeroLineMellinWeight V Z t‖) =
      (1/(2*Real.pi))*(∫ t : ℝ, |t|^A*‖mellin V ((t:ℂ)*Complex.I)‖) := by
  simp_rw [zeroLineMellinWeight_norm V hZ]
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothNormPartition
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit finite smooth partition on every bounded positive norm range.
Its fixed weight is supported in `[1,2]`, as required by the smooth
short-factor estimates. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma normPartitionWeight_norm (x : ℝ) : ‖normPartitionWeight x‖ ≤ 1 := by
  by_cases hx : x < 1
  · rw [normPartitionWeight_low hx,norm_zero]
    norm_num
  have hmono : normPartitionStep (3*x/4) ≤ normPartitionStep x :=
    Real.smoothTransition.monotone (by linarith)
  have hnonneg := Real.smoothTransition.nonneg (3*(3*x/4-1))
  have hone := Real.smoothTransition.le_one (3*(x-1))
  rw [normPartitionWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hmono)]
  dsimp [normPartitionStep] at *
  linarith

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoordinateWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform joint Mellin moments from the actual common support and derivative
bounds of the coordinate weights. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellinMass_nonneg (W : ℝ → ℂ) : 0 ≤ zeroLineMellinMass W := by
  unfold zeroLineMellinMass
  positivity

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramMellinTwist
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of the existing Poisson/Mellin kernel's Fourier
frequency to the norm heights used by the proved structured moments. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_add_height (u v x : ℝ) :
    mellinPhase (u+v) x = mellinPhase u x*mellinPhase v x := by
  unfold mellinPhase
  rw [show (((u+v)*Real.log x:ℝ):ℂ)*Complex.I =
    ((u*Real.log x:ℝ):ℂ)*Complex.I+((v*Real.log x:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormMellinMoments
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrated decay with polynomial Mellin-height weights. This controls
truncated shifts in the dispersion kernel. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma mellin_window_majorant {g : ℝ → ℝ} {B C T : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : 0 < T) (k : ℕ) (hg : ∀ t, g t ≤ C) (hsmall : ∀ t, ‖t‖ ≤ T → g t ≤ B) (t : ℝ) :
    g t ≤ B+C/T^k*‖t‖^k := by
  by_cases ht : ‖t‖ ≤ T
  · exact (hsmall t ht).trans (le_add_of_nonneg_right (by positivity))
  · have hp : T^k ≤ ‖t‖^k := pow_le_pow_left₀ hT.le (le_of_not_ge ht) _
    have hratio : 1 ≤ ‖t‖^k/T^k := (le_div_iff₀ (pow_pos hT _)).mpr (by simpa using hp)
    calc
      _ ≤ C := hg t
      _ ≤ C*(‖t‖^k/T^k) := le_mul_of_one_le_right hC hratio
      _ = C/T^k*‖t‖^k := by ring
      _ ≤ B+C/T^k*‖t‖^k := le_add_of_nonneg_left hB


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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonEntryDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonTailPower
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary power gap for a cutoff beyond the natural Poisson
scale. The number of integrations by parts is fixed from the gap. -/
noncomputable section
namespace CubicFirstMoment

lemma poisson_cutoff_exists {L η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hlarge : 2 ≤ L^(η/2)) :
    ∃ n : ℕ, L^(1+η/2) ≤ (2:ℝ)^n ∧
      ∀ j : ℕ, j < n → 2*(2:ℝ)^j ≤ L^(1+η) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hx : 1 ≤ L^(1+η/2) := Real.one_le_rpow hL (by linarith)
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ) < 2)
  refine ⟨n+1,hn'.le,?_⟩
  have hup : (2:ℝ)^(n+1) ≤ L^(1+η) := by
    calc
      _ ≤ 2*L^(1+η/2) := by rw [pow_succ]; nlinarith
      _ ≤ L^(η/2)*L^(1+η/2) := mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring
  intro j hj
  calc
    _ = (2:ℝ)^(j+1) := by rw [pow_succ]; ring
    _ ≤ (2:ℝ)^(n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ _ := hup

lemma poisson_cutoff_scale {L A J K η : ℝ} (hL : 1 ≤ L) (hη : η ≤ 1)
    (hA : L^(1-η/4) ≤ A) (hJ : L^(1+η/2) ≤ J) (hK : 0 < K) :
    1/(K*L^2) ≤ A/(K*L^2) ∧
      L^(η/4)/K ≤ (A/(K*L^2))*J := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA₁ : 1 ≤ A := (Real.one_le_rpow hL (by linarith)).trans hA
  constructor
  · exact div_le_div_of_nonneg_right hA₁ (by positivity)
  · have hpow : L^(1-η/4)*L^(1+η/2) = L^(η/4)*L^2 := by
      rw [← Real.rpow_add hLp,← Real.rpow_natCast L 2,← Real.rpow_add hLp]
      congr 1
      push_cast
      ring
    calc
      _ = (L^(1-η/4)*L^(1+η/2))/(K*L^2) := by rw [hpow]; field_simp
      _ ≤ (A*J)/(K*L^2) := div_le_div_of_nonneg_right
        (mul_le_mul hA hJ (by positivity) (by linarith)) (by positivity)
      _ = _ := by ring

lemma poisson_tail_power_gap {L A t J K α : ℝ} (hL : 1 ≤ L) (_hA : 0 ≤ A)
    (hAL : A ≤ L^2) (ht : 0 < t) (hJ : 0 < J) (hK : 0 < K)
    (htL : 1/(K*L^2) ≤ t) (hcut : L^α/K ≤ t*J)
    (m : ℕ) (hm : 11 ≤ α*m) :
    A*L*t^(-3:ℝ)/(t*J)^m ≤ K^(m+3)*L^(-2:ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hit : t⁻¹ ≤ K*L^2 := by
    rw [← one_div,div_le_iff₀ ht]
    have hh := (div_le_iff₀ (show 0 < K*L^2 by positivity)).mp htL
    nlinarith
  have ht3 : t^(-3:ℝ) ≤ K^3*L^6 := by
    rw [Real.rpow_neg ht.le,Real.rpow_ofNat,← inv_pow]
    apply (pow_le_pow_left₀ (by positivity) hit 3).trans_eq
    ring
  have hiq : (t*J)⁻¹ ≤ K/(L^α) := by
    rw [← one_div,div_le_iff₀ (mul_pos ht hJ),div_mul_eq_mul_div]
    have hh := (div_le_iff₀ hK).mp hcut
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hLp α)).mpr
    nlinarith
  have hqm : ((t*J)^m)⁻¹ ≤ K^m*L^(-(α*m)) := by
    rw [← inv_pow]
    apply (pow_le_pow_left₀ (by positivity) hiq m).trans_eq
    rw [div_pow,← Real.rpow_mul_natCast hLp.le,Real.rpow_neg hLp.le]
    ring
  have hAp : A*L ≤ L^3 := by nlinarith
  calc
    _ ≤ L^3*(K^3*L^6)*(K^m*L^(-(α*m))) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul hAp ht3 (Real.rpow_nonneg ht.le _) (by positivity))
        hqm (by positivity) (by positivity)
    _ = K^(m+3)*L^(9-α*m) := by
      rw [pow_add,Real.rpow_sub hLp]
      rw [Real.rpow_ofNat,Real.rpow_neg hLp.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

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

lemma dyadicHeightMean_le_const {f : ℝ → ℝ} (hf : Continuous f)
    {T C : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ C) :
    dyadicHeightMean f T ≤ 2*C :=
  (dyadicHeightMean_mono hf continuous_const hT h).trans_eq
    (dyadicHeightMean_const C hT.ne')

lemma dyadicHeightMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (T : ℝ) :
    dyadicHeightMean (fun t => f t+g t) T = dyadicHeightMean f T+dyadicHeightMean g T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_add
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

lemma dyadicHeightMean_const_mul (c : ℝ) (f : ℝ → ℝ) (T : ℝ) :
    dyadicHeightMean (fun t => c*f t) T = c*dyadicHeightMean f T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Fubini for a bounded height polynomial and an integrable
Mellin weight. No mean estimate or interchange is assumed. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma continuous_height_convolution {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) :
    Continuous (fun t => ∫ s : ℝ, f s*G (t+u+s)) := by
  apply continuous_of_dominated (bound := fun s => ‖f s‖*M)
  · intro t
    exact (hf.mul (hG.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · intro t
    filter_upwards with s
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound _) (_root_.norm_nonneg _)
  · exact hfi.norm.mul_const M
  · filter_upwards with s
    exact continuous_const.mul (hG.comp ((continuous_id.add continuous_const).add continuous_const))

lemma integrable_height_convolution_kernel {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun p : ℝ × ℝ => f p.1*G (p.2+u+p.1))
      (volume.prod (volume.restrict (Icc a b))) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ × ℝ → ℝ := fun p => f p.1*G (p.2+u+p.1)
  have hc : Continuous K :=
    (hf.comp continuous_fst).mul (hG.comp ((continuous_snd.add continuous_const).add continuous_fst))
  have hm : AEStronglyMeasurable K (volume.prod μ) := hc.aestronglyMeasurable
  have hb (s : ℝ) : (∫ t, ‖K (s,t)‖ ∂μ) ≤ (b-a)*M*‖f s‖ := by
    have hki : IntervalIntegrable (fun t => ‖K (s,t)‖) volume a b :=
      ((hc.comp (continuous_const.prodMk continuous_id)).norm).intervalIntegrable a b
    have hi := intervalIntegral.integral_mono_on hab hki
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖f s‖*M) volume a b)
      (fun t _ => by
        dsimp [K]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg (f s)))
    rw [intervalIntegral.integral_const,smul_eq_mul] at hi
    simpa only [μ,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
      mul_comm,mul_left_comm,mul_assoc] using hi
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun s =>
    (hc.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc),?_⟩
  apply (hfi.norm.const_mul ((b-a)*M)).mono' hm.norm.integral_prod_right'
  exact Filter.Eventually.of_forall (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => _root_.norm_nonneg _))]
    exact hb s)

lemma height_convolution_interval_swap {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ∫ s : ℝ, f s*G (t+u+s)) =
      ∫ s : ℝ, f s*(∫ t in a..b, G (t+u+s)) := by
  have hi := integrable_height_convolution_kernel hf hfi hG hbound u hab
  have hs := (integral_integral_swap (f := fun s t : ℝ => f s*G (t+u+s)) hi).symm
  simp only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab] at hs
  rw [hs]
  apply integral_congr_ae
  filter_upwards with s
  exact intervalIntegral.integral_const_mul _ _

lemma integrable_height_convolution_interval {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun s : ℝ => f s*(∫ t in a..b, G (t+u+s))) := by
  have hi := (integrable_height_convolution_kernel hf hfi hG hbound u hab).integral_prod_left
  simp only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_const_mul] at hi
  exact hi

theorem dyadicHeightMean_convolution {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+s)) T =
      ∫ s : ℝ, f s*dyadicHeightMean (fun t => G (t+u+s)) T := by
  have hp : T ≤ 2*T := by linarith
  have hn : -2*T ≤ -T := by linarith
  have hip := integrable_height_convolution_interval hf hfi hG hbound u hp
  have hin := integrable_height_convolution_interval hf hfi hG hbound u hn
  rw [dyadicHeightMean,height_convolution_interval_swap hf hfi hG hbound u hp,
    height_convolution_interval_swap hf hfi hG hbound u hn,← integral_add hip hin,← integral_div]
  apply integral_congr_ae
  filter_upwards with s
  dsimp [dyadicHeightMean]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightConvolutionBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A height bound on the central Mellin window and the actual moment
tail of the Mellin weight suffice for the averaged convolution. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma integrable_height_convolution_mean {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun s => f s*dyadicHeightMean (fun t => G (t+u+s)) T) := by
  have hp := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : T ≤ 2*T)
  have hn := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : -2*T ≤ -T)
  convert (hp.add hn).div_const T using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  dsimp [dyadicHeightMean]
  ring

theorem dyadicHeightMean_convolution_window {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hf0 : ∀ s, 0 ≤ f s)
    (hG : Continuous G) {M B S T : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) (n : ℕ)
    (hfm : Integrable (fun s => ‖s‖^n*f s))
    (hsmall : ∀ s, ‖s‖ ≤ S →
      dyadicHeightMean (fun t => G (t+u+s)) T ≤ B) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+s)) T ≤
      B*(∫ s : ℝ, f s)+(2*M)/S^n*(∫ s : ℝ, ‖s‖^n*f s) := by
  let H := fun s => dyadicHeightMean (fun t => G (t+u+s)) T
  have hglobal (s : ℝ) : H s ≤ 2*M := by
    apply dyadicHeightMean_le_const (hG.comp (by fun_prop)) hT
    intro t _
    exact (le_abs_self _).trans (hbound (t+u+s))
  rw [dyadicHeightMean_convolution hf hfi hG hbound u hT]
  calc
    _ ≤ ∫ s : ℝ, B*f s+((2*M)/S^n)*(‖s‖^n*f s) := by
      apply integral_mono (integrable_height_convolution_mean hf hfi hG hbound u hT)
        ((hfi.const_mul B).add (hfm.const_mul ((2*M)/S^n)))
      intro s
      have hh := mellin_window_majorant hB (by positivity : 0 ≤ 2*M) hS n hglobal hsmall s
      calc
        _ ≤ f s*(B+(2*M)/S^n*‖s‖^n) := mul_le_mul_of_nonneg_left hh (hf0 s)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = _ := by rw [integral_add (hfi.const_mul B) (hfm.const_mul ((2*M)/S^n)),
      integral_const_mul,integral_const_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightMeanSquare
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightPoissonAnnulus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightPoissonTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete absolute Poisson tail for angular coefficients, with unchanged
coefficient energies and every frequency retained. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

theorem angular_logarithmic_absolute_poisson_dyad {R : ℝ} (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ (K : ℝ) (a : ℕ), 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (A : ℝ) (e : Eisenstein) (u : ℝ) (j : ℕ) (H : Finset Eisenstein),
      0 < A → H ⊆ frequencyDyad j →
      ‖finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e) H
        (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A*L r*(1+Real.log (L r))^a*(2:ℝ)^j /
          (1+A*(2:ℝ)^j/(27*(R^Fintype.card ι*L r)^2))^m := by
  obtain ⟨C,hC,hbound⟩ := finitePoissonContribution_absolute V hV hV' m
  obtain ⟨E,a,hE,hl1⟩ := logarithmic_full_l1_square hR hW hlo hhi
  refine ⟨4*C*E,a,by positivity,?_⟩
  intro r X hL hX hprod A e u j H hA hH
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hRpow : 1 ≤ R^Fintype.card ι := one_le_pow₀ hR
  have hS : ∀ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      primary b ∧ L r ≤ norm b ∧ norm b ≤ R^Fintype.card ι*L r := by
    intro b hb
    have hn := fullPrimeProduct_norm_bounds R (W r) X
      (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) (Finset.mem_filter.mp hb).1
    rw [hprod] at hn
    exact ⟨(fullSquarefreePrimeSupport_primary R (W r) X e hb).1,hn⟩
  have hm := hbound A (L r) (R^Fintype.card ι*L r) ((2:ℝ)^j) hA hLp
    (le_mul_of_one_le_left hLp.le hRpow) (by positivity) _ H hS
    (fun h hh => (frequencyDyad_norm (hH hh)).1) (angularHeightPrimeCoefficient ℓ R (W r) X) u
  have hc₀ : (H.card:ℝ) ≤ ((frequencyDyad j).card:ℝ) := by exact_mod_cast Finset.card_le_card hH
  have hc : (H.card:ℝ) ≤ 36*(2:ℝ)^j := hc₀.trans (frequencyDyad_card_le j)
  rw [angularHeightPrimeCoefficient_l1] at hm
  apply hm.trans
  calc
    _ ≤ C*(A/(9*L r))*(36*(2:ℝ)^j)*(E*(L r)^2*(1+Real.log (L r))^a) /
        (1+A*(2:ℝ)^j/(27*(R^Fintype.card ι*L r)^2))^m := by
      gcongr
      exact hl1 r X hL hX hprod e
    _ = _ := by field_simp; ring


theorem angular_logarithmic_poisson_tail {R : ℝ} (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ (K : ℝ) (a : ℕ), 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (A : ℝ) (e : Eisenstein) (u : ℝ) (n : ℕ) (H : ℕ → Finset Eisenstein),
      0 < A → (∀ j, H j ⊆ frequencyDyad j) →
      let t := A/(27*(R^Fintype.card ι*L r)^2)
      Summable (fun j => finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        (K*A*L r*(1+Real.log (L r))^a/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  obtain ⟨K,a,hK,hbound⟩ := angular_logarithmic_absolute_poisson_dyad ℓ hR hW hlo hhi V hV hV' (m+3)
  refine ⟨K,a,hK,?_⟩
  intro r X hL hX hprod A e u n H hA hH
  dsimp only
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  let t := A/(27*(R^Fintype.card ι*L r)^2)
  let C := K*A*L r*(1+Real.log (L r))^a
  let F := fun j => finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
    (H j) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A
  have ht : 0 < t := by dsimp [t]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrow (j : ℕ) : ‖F j‖ ≤ C*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3) := by
    have heq : t*(2:ℝ)^j = A*(2:ℝ)^j/(27*(R^Fintype.card ι*L r)^2) := by
      dsimp [t]
      ring
    rw [heq]
    exact hbound r X hL hX hprod A e u j (H j) hA (hH j)
  exact poisson_dyadic_tail ht hC m n F hrow


theorem angular_high_poisson_log_saving {R η : ℝ} (hR : 1 ≤ R) (hη : 0 < η) (hη₁ : η ≤ 1)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ),
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (A : ℝ) (e : Eisenstein) (u : ℝ) (n : ℕ) (H : ℕ → Finset Eisenstein),
      L r ^ (1-η/4) ≤ A → A ≤ (L r)^2 →
      L r ^ (1+η/2) ≤ (2:ℝ)^n → (∀ j, H j ⊆ frequencyDyad j) →
      Summable (fun j => finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤ K/(1+Real.log (L r))^k := by
  obtain ⟨m,hm⟩ := exists_nat_gt (44/η)
  have hm' : 11 ≤ (η/4)*(m:ℝ) := by
    have hh := (div_lt_iff₀ hη).mp hm
    nlinarith
  obtain ⟨K,a,hK,hbound⟩ := angular_logarithmic_poisson_tail ℓ hR hW hlo hhi V hV hV' m
  let D := 27*(R^Fintype.card ι)^2
  have hD : 0 < D := by dsimp [D]; positivity
  let C := 2*K*D^(m+3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (by norm_num : (0:ℝ) < 2) (a+k))
  refine ⟨C+1,T₀,by positivity,?_⟩
  intro r X hT₀ hL hX hprod A e u n H hAlo hAhi hcut hH
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hA₁ : 1 ≤ A := (Real.one_le_rpow hL (by linarith)).trans hAlo
  have hA : 0 < A := zero_lt_one.trans_le hA₁
  let t := A/(D*(L r)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have heq : A/(27*(R^Fintype.card ι*L r)^2) = t := by dsimp [t,D]; ring
  have hb := hbound r X hL hX hprod A e u n H hA hH
  dsimp only at hb
  rw [heq] at hb
  refine ⟨hb.1,?_⟩
  have hscale := poisson_cutoff_scale hL hη₁ hAlo hcut hD
  have hp := poisson_tail_power_gap hL hA.le hAhi ht (by positivity : 0 < (2:ℝ)^n)
    hD hscale.1 hscale.2 m hm'
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hgeo : ((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹ ≤ 2 := by
    norm_num
    have hh : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hlog : (1+Real.log (L r))^a*(L r)^(-2:ℝ) ≤ 1/(1+Real.log (L r))^k := by
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  calc
    _ ≤ (K*A*L r*(1+Real.log (L r))^a/(t*(2:ℝ)^n)^m)*
        (t^(-3:ℝ)*2) := hb.2.trans (mul_le_mul_of_nonneg_left
          (by nlinarith [mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg ht.le (-3))]) (by positivity))
    _ = (2*K*(1+Real.log (L r))^a)*(A*L r*t^(-3:ℝ)/(t*(2:ℝ)^n)^m) := by ring
    _ ≤ (2*K*(1+Real.log (L r))^a)*(D^(m+3)*(L r)^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C*((1+Real.log (L r))^a*(L r)^(-2:ℝ)) := by dsimp [C]; ring
    _ ≤ C*(1/(1+Real.log (L r))^k) := mul_le_mul_of_nonneg_left hlog hC
    _ ≤ _ := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightPoissonTotal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete nonzero Poisson frequency series has an averaged
logarithmic saving. Its infinite tail is controlled uniformly in height. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_height_poisson_total_saving
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (H : ℕ → Finset Eisenstein)
        (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → (∀ j, H j ⊆ frequencyDyad j) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      dyadicHeightMean (fun t => ‖∑' j : ℕ,
        finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e) (H j)
          (angularHeightPrimeCoefficient ℓ R (W r) X) (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hshort⟩ := angular_height_poisson_dyadic_saving ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,L₁,m,hK₁,hshort⟩ := hshort L W hL hW hlo hhi
  obtain ⟨K₂,L₂,hK₂,htail⟩ := angular_high_poisson_log_saving ℓ hR hη hη₁ hW hlo hhi V hV hV' k
  obtain ⟨L₃,hL₃⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < η/2 by positivity)).eventually_ge_atTop 2)
  obtain ⟨K₀,a,_hK₀,henv⟩ := angular_logarithmic_absolute_poisson_dyad ℓ hR hW hlo hhi V hV hV' 3
  refine ⟨K₁+2*K₂,max L₁ (max L₂ L₃),m,by positivity,?_⟩
  intro r X A H e u T hL₀ hprod hX hAlo hAhi hH he heN hT hThi hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hA₁ : 1 ≤ A := (Real.one_le_rpow (hL r) (by linarith)).trans hAlo
  have hA : 0 < A := zero_lt_one.trans_le hA₁
  have hX₁ : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hL₁ := (le_max_left L₁ (max L₂ L₃)).trans hL₀
  have hL₂ := (le_max_left L₂ L₃).trans ((le_max_right L₁ (max L₂ L₃)).trans hL₀)
  have hL₃' := (le_max_right L₂ L₃).trans ((le_max_right L₁ (max L₂ L₃)).trans hL₀)
  obtain ⟨n,hn,hprefix⟩ := poisson_cutoff_exists (hL r) hη.le (hL₃ (L r) hL₃')
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := angularHeightPrimeCoefficient ℓ R (W r) X
  let F := fun j v => finitePoissonContribution S (H j) β (u+v) V A
  have hfc (j : ℕ) : Continuous (F j) :=
    (finitePoissonContribution_continuous_height S (H j) β V A).comp (continuous_const.add continuous_id)
  let t := A/(27*(R^Fintype.card ι*L r)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have htotal : Continuous (fun v => ∑' j : ℕ, F j v) :=
    continuous_poisson_series S H β V A u (C := K₀*A*L r*(1+Real.log (L r))^a) ht (fun j v => by
      have hh := henv r X (hL r) hX₁ hprod A e (u+v) j (H j) hA (hH j)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [t]
      ring)
  have hpre := hshort r X A (Finset.range n) H e u T hL₁ hprod hX hA
    (fun j hj => hprefix j (Finset.mem_range.mp hj)) hH he heN hT hThi hu
  have hpoint (v : ℝ) : ‖∑' j : ℕ, F j v‖ ≤
      ‖∑ j ∈ Finset.range n, F j v‖+K₂/(1+Real.log (L r))^k := by
    obtain ⟨hfs,hft⟩ := htail r X hL₂ (hL r) hX₁ hprod A e (u+v) n H hAlo hAhi hn hH
    exact norm_tsum_prefix_tail n hfs le_rfl hft
  have hsumc := continuous_finsetSum (Finset.range n) (fun j _ => hfc j)
  have hm := dyadicHeightMean_mono htotal.norm (hsumc.norm.add continuous_const) hTp
    (fun v _ => hpoint v)
  change dyadicHeightMean (fun v => ‖∑' j : ℕ, F j v‖) T ≤
    dyadicHeightMean (fun v => ‖∑ j ∈ Finset.range n, F j v‖+K₂/(1+Real.log (L r))^k) T at hm
  rw [dyadicHeightMean_add hsumc.norm continuous_const,dyadicHeightMean_const _ hTp.ne'] at hm
  have hscale : 1 ≤ A^(2/3:ℝ)*(L r)^(5/3:ℝ) := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hA₁ (by norm_num)) (Real.one_le_rpow (hL r) (by norm_num))
  apply hm.trans
  calc
    _ ≤ K₁*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k+
        2*(K₂/(1+Real.log (L r))^k) := add_le_add hpre le_rfl
    _ ≤ K₁*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k+
        2*(K₂*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))/(1+Real.log (L r))^k) := by
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hK₂.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimePoissonSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightCoprimeDispersion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The averaged estimate for the original coprime Gram form, obtained
from the complete Poisson series without omitting any frequencies. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_height_coprime_dispersion_saving
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      dyadicHeightMean (fun t =>
        ‖coprimeDispersionGram (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hseries⟩ := angular_height_poisson_total_saving ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K,L₀,m,hK,hseries⟩ := hseries L W hL hW hlo hhi
  refine ⟨K,max L₀ 2,m,hK,?_⟩
  intro r X A e u T hL₀ hprod hX hAlo hAhi he heN hT hThi hu
  have hL₂ : 2 ≤ L r := (le_max_right L₀ 2).trans hL₀
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hXpos : ∀ i, 0 < X i := fun i =>
    (Real.rpow_pos_of_pos (by linarith : 0 < 2*L r) c).trans (hX i)
  have hS : ∀ a ∈ fullSquarefreePrimeSupport R (W r) X e,
      primary a ∧ Squarefree a ∧ a ≠ 1 := by
    intro a ha
    refine ⟨(fullSquarefreePrimeSupport_primary R (W r) X e ha).1,
      (fullSquarefreePrimeSupport_primary R (W r) X e ha).2,?_⟩
    have hn := (fullPrimeProduct_norm_bounds R (W r) X hXpos (hlo r) (hhi r)
      (Finset.mem_filter.mp ha).1).1
    rw [hprod] at hn
    intro h
    rw [h,norm_one_eq] at hn
    linarith
  have hident (t : ℝ) := coprimeDispersionGram_eq_poisson_series _ hS
    (angularHeightPrimeCoefficient ℓ R (W r) X) (u+t) V hV hV' hA
  simp_rw [hident]
  exact hseries r X A frequencyDyad e u T ((le_max_left L₀ 2).trans hL₀)
    hprod hX hAlo hAhi (fun _ => Finset.Subset.refl _) he heN hT hThi hu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightGramContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma divisorDispersionVariance_one (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (A : ℝ) :
    divisorDispersionVariance 1 S β u V A = smoothedDispersionVariance S β u V A := by
  simp only [divisorDispersionVariance,smoothedDispersionVariance,one_pow,one_dvd,and_true]

lemma divisorCoprimeDispersionGram_one (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ) (A : ℝ) :
    divisorCoprimeDispersionGram 1 S β u V A = coprimeDispersionGram S β u V A := by
  unfold divisorCoprimeDispersionGram
  rw [norm_one_eq,one_pow,div_one]
  unfold coprimeDispersionGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hca : cubicSymbol a 1 = 1 := (cubic_reciprocity (hS a ha) primary_one).trans (cubicSymbol_one_lower a)
  have hcb : cubicSymbol b 1 = 1 := (cubic_reciprocity (hS b hb) primary_one).trans (cubicSymbol_one_lower b)
  simp only [dispersionAmplitude,divisorTwistedCoefficient,one_pow,hca,hcb,star_one,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightFullVariance
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual full variance has the required averaged upper bound.
The shared-prime remainder is uniform in height and is retained. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_height_full_variance_saving
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hcop⟩ := angular_height_coprime_dispersion_saving ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k
  refine ⟨min η c,σ,lt_min hη hc,(min_le_left _ _).trans hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,L₁,m,hK₁,hcop⟩ := hcop L W hL hW hlo hhi
  have hηc : min η c/4 ≤ c := by linarith [min_le_right η c]
  obtain ⟨G,K₂,L₂,hK₂,hrem⟩ := angular_fullPrime_divisor_noncoprime_log_saving ℓ
    (η := min η c/4) hR hc hc₁ hηc hW hlo hhi V hV hV' k
  refine ⟨G,K₁+2*K₂,max L₁ L₂,m,by positivity,?_⟩
  intro r X A e u T hL₀ hprod hX hAlo hAhi he heN hT hThi hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos (zero_lt_one.trans_le hz) m).trans_le hT
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hA₂ : A ≤ (L r)^2 := hAhi.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hz))
  have hAcop : (L r)^(1-η/4) ≤ A :=
    (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [min_le_left η c])).trans hAlo
  have hX₁ : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hrough : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hX i)
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := angularHeightPrimeCoefficient ℓ R (W r) X
  have hS : ∀ a ∈ S, primary a := fun a ha => (fullSquarefreePrimeSupport_primary R (W r) X e ha).1
  let E := K₂*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k
  have hr (v : ℝ) : ‖smoothedDispersionVariance S β v V A-coprimeDispersionGram S β v V A‖ ≤ E := by
    have hh := hrem r X A 1 e v ((le_max_right L₁ L₂).trans hL₀) (hL r) hX₁ hprod hrough
      primary_one (by simpa only [norm_one_eq] using hL r) hAlo hAhi
    rwa [divisorDispersionVariance_one,divisorCoprimeDispersionGram_one _ hS] at hh
  have hvc : Continuous (fun t : ℝ => smoothedDispersionVariance S β (u+t) V A) := (continuous_smoothedDispersionVariance S hS β V hV hV' hA).comp
    (continuous_const.add continuous_id)
  have hcc : Continuous (fun t : ℝ => coprimeDispersionGram S β (u+t) V A) := (continuous_coprimeDispersionGram S β V A).comp (continuous_const.add continuous_id)
  have havg := dyadicHeightMean_mono (g := fun v => ‖coprimeDispersionGram S β (u+v) V A‖+E)
    hvc.norm (hcc.norm.add continuous_const) hTp (fun v _ => by
    have h := (norm_add_le
      (smoothedDispersionVariance S β (u+v) V A-coprimeDispersionGram S β (u+v) V A)
      (coprimeDispersionGram S β (u+v) V A)).trans (add_le_add (hr (u+v)) le_rfl)
    rw [sub_add_cancel] at h
    exact h.trans_eq (add_comm _ _))
  change dyadicHeightMean (fun v => ‖smoothedDispersionVariance S β (u+v) V A‖) T ≤
    dyadicHeightMean (fun v => ‖coprimeDispersionGram S β (u+v) V A‖+E) T at havg
  rw [dyadicHeightMean_add hcc.norm continuous_const,dyadicHeightMean_const _ hTp.ne'] at havg
  have hb := hcop r X A e u T ((le_max_left L₁ L₂).trans hL₀) hprod hX
    hAcop hA₂ he heN hT hThi hu
  apply havg.trans
  exact (add_le_add hb le_rfl).trans_eq (by dsimp [E]; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedBilinearScale
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic saving furnished by corrected Cauchy--Schwarz. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bilinear_error_log_saving {x : ℂ} {M K A L z E V : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 < A) (hL : 0 < L) (hz : 0 < z)
    (k d : ℕ) (_hE : 0 ≤ E) (hV : 0 ≤ V)
    (herror : ‖x‖^2 ≤ E*V) (henergy : E ≤ M*A*z^d)
    (hmass : V ≤ K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) :
    ‖x‖ ≤ Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  have hsqA : (A^(5/6:ℝ))^2 = A^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (A^(5/6:ℝ)) 2,←Real.rpow_mul hA.le]
    norm_num
  have hsqL : (L^(5/6:ℝ))^2 = L^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (L^(5/6:ℝ)) 2,←Real.rpow_mul hL.le]
    norm_num
  have hAadd : A*A^(2/3:ℝ) = A^(5/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one A]
    rw [←Real.rpow_add hA]
    norm_num
  have hid : (Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k)^2 =
      (M*A*z^d)*(K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hM hK),hsqA,hsqL,
      pow_add,pow_mul]
    field_simp
    simp only [←pow_mul]
    rw [Nat.mul_comm 2 k,←hAadd]
    ring
  have hb := herror.trans (mul_le_mul henergy hmass hV (by positivity))
  rw [←hid] at hb
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp hb

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

lemma dyadicHeightMean_nonneg {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ}
    (hT : 0 < T) (h : ∀ t, 0 ≤ f t) : 0 ≤ dyadicHeightMean f T := by
  have hm := dyadicHeightMean_mono continuous_const hf hT (fun t _ => h t)
  simpa only [dyadicHeightMean_const 0 hT.ne',mul_zero] using hm

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

lemma height_bilinear_error_log_saving {f : ℝ → ℂ} (hf : Continuous f)
    {T M K A L z E V : ℝ} (hT : 0 < T)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 < A) (hL : 0 < L) (hz : 0 < z)
    (k d : ℕ) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (herror : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ E*V)
    (henergy : E ≤ M*A*z^d)
    (hmass : V ≤ K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤
      (2*(Real.sqrt (M*K)+1))*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  let B := dyadicHeightMean (fun t => ‖f t‖^2) T
  have hB : 0 ≤ B := dyadicHeightMean_nonneg (hf.norm.pow 2) hT (fun _ => sq_nonneg _)
  have hroot : ‖(Real.sqrt B:ℂ)‖^2 ≤ E*V := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hB]
    exact herror
  have hb := bilinear_error_log_saving hM hK hA hL hz k d hE hV hroot henergy hmass
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hb
  let R := (Real.sqrt (M*K)+1)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k
  have hR : 0 < R := by dsimp [R]; positivity
  have hbr : Real.sqrt B ≤ R := hb.trans (by
    dsimp [R]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : Real.sqrt (M*K) ≤ Real.sqrt (M*K)+1)
          (Real.rpow_nonneg hA.le _)) (Real.rpow_nonneg hL.le _)) (pow_nonneg hz.le _))
  have hsq : B ≤ R^2 := by nlinarith [Real.sq_sqrt hB,Real.sqrt_nonneg B]
  have hm := dyadicHeightMean_norm_le_of_sq_le hf hT hR hsq
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [R]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightBilinearScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the genuine height-averaged bilinear estimate. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_rough_prime_height_bilinear
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R Q M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hM : 0 ≤ M)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (k d : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u T : ℝ)
        (P : Finset Eisenstein) (α : Eisenstein → ℂ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      (∀ a ∈ P, primary a ∧ norm a/A ∈ Set.Icc 1 Q) →
      (∑ a ∈ P, ‖α a‖^2) ≤ M*A*(1+Real.log (L r))^d →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
          α a*angularHeightPrimeCoefficient ℓ R (W r) X b*gauss (a*b)*normTwist (u+t) (a*b)‖) T ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hvar⟩ := angular_height_full_variance_saving ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    (fun x => (dispersionCutoff Q x:ℂ)) (dispersionCutoff_complex_compact Q)
    (dispersionCutoff_complex_smooth Q) (2*k+d)
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨G,K₀,L₀,m,hK₀,hvar⟩ := hvar L W hL hW hlo hhi
  refine ⟨G,2*(Real.sqrt (M*K₀)+1),L₀,m,by positivity,?_⟩
  intro r X A e u T P α hL₀ hprod hX hAlo hAhi he heN hT hThi hu hP henergy
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hAp : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := angularHeightPrimeCoefficient ℓ R (W r) X
  have hS : ∀ b ∈ S, primary b := fun b hb => (fullSquarefreePrimeSupport_primary R (W r) X e hb).1
  have hcont : Continuous (fun t => ∑ a ∈ P, ∑ b ∈ S,
      α a*β b*gauss (a*b)*normTwist (u+t) (a*b)) := by
    apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    exact continuous_const.mul ((continuous_normTwist (a*b)).comp (continuous_const.add continuous_id))
  exact height_bilinear_error_log_saving hcont hTp hM hK₀.le hAp hLp hz k d
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (dyadicHeightMean_nonneg
      (((continuous_smoothedDispersionVariance S hS β (fun x => (dispersionCutoff Q x:ℂ))
        (dispersionCutoff_complex_compact Q) (dispersionCutoff_complex_smooth Q) hAp).comp
          (continuous_const.add continuous_id)).norm) hTp (fun _ => _root_.norm_nonneg _))
    (height_bilinear_full_variance_bound_sq P S α β u (fun a ha => (hP a ha).1) hS
      (dispersionCutoff Q) (dispersionCutoff_nonneg Q) (dispersionCutoff_complex_compact Q)
      (dispersionCutoff_complex_smooth Q) hAp hTp
      (fun a ha => (dispersionCutoff_one (hP a ha).2).ge))
    henergy (hvar r X A e u T hL₀ hprod hX hAlo hAhi he heN hT hThi hu)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KernelScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scaling a cutoff kernel

The normalization and weighted L¹ moment are preserved under `T k(Tx)`.
Thus a single Schwartz kernel gives a uniform family of interval
approximations at all positive truncation heights.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

theorem integrable_scaledKernel {k : ℝ → ℂ} (hk : Integrable k)
    {T : ℝ} (hT : 0 < T) : Integrable (scaledKernel k T) :=
  (hk.comp_mul_left' hT.ne').const_mul (T : ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FourierCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete Fourier cutoff kernel

The fixed cutoff is a smooth bump, one near zero and supported in [-1,1].
Its inverse Fourier transform is a normalized Schwartz kernel. Mathlib
uses exp(2π i x ξ); this frequency variable differs by 2π from the
height variable in the manuscript.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform

namespace CubicFirstMoment

theorem frequencyCutoff_apply (x : ℝ) : frequencyCutoff x = (frequencyBump x : ℂ) := rfl

theorem frequencyCutoff_zero {x : ℝ} (hx : 1 ≤ |x|) : frequencyCutoff x = 0 := by
  rw [frequencyCutoff_apply, frequencyBump.zero_of_le_dist]
  · rfl
  · simpa only [Real.dist_eq, sub_zero, frequencyBump] using hx

/-- Inversion identifies the Fourier transform with the actual compact cutoff. -/
theorem fourier_truncationKernel : 𝓕 truncationKernel = frequencyCutoff :=
  fourier_fourierInv_eq frequencyCutoff

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FourierSmoothing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Frequency support of the concrete interval smoothing

The convolution has Fourier transform equal to the interval transform
times the actual compactly supported cutoff. This connects the physical
endpoint bounds with truncation in the height variable.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform Convolution

namespace CubicFirstMoment

/-- Dilation of the kernel dilates its Fourier support by exactly the same factor. -/
theorem fourier_scaledKernel (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) (ξ : ℝ) :
    𝓕 (scaledKernel k T) ξ = 𝓕 k (ξ/T) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  let f : ℝ → ℂ := fun y => Complex.exp ((-2 * Real.pi * y * (ξ/T) : ℝ) * Complex.I) * k y
  have he : (fun y => Complex.exp ((-2 * Real.pi * y * ξ : ℝ) * Complex.I) *
      scaledKernel k T y) = (fun y => (T : ℂ) * f (T*y)) := by
    funext y
    have he : -2 * Real.pi * (T*y) * (ξ/T) = -2 * Real.pi * y * ξ := by field_simp
    simp only [f, scaledKernel, he]
    ring
  rw [he, integral_const_mul, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr hT), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hT.ne', Complex.ofReal_one, one_mul, f]

theorem integrable_intervalStep (a b : ℝ) :
    Integrable (fun x => (intervalStep a b x : ℂ)) := by
  have h : Integrable ((Set.Icc a b).indicator (fun _ : ℝ => (1 : ℂ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)
  have he : (fun x => (intervalStep a b x : ℂ)) =
      (Set.Icc a b).indicator (fun _ : ℝ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;>
      simp only [intervalStep, Set.indicator_apply, hx, ite_true, if_true, ite_false, if_false,
        Complex.ofReal_one, Complex.ofReal_zero]
  rwa [he]

theorem intervalSmoothing_eq_convolution (k : ℝ → ℂ) (a b : ℝ) :
    intervalSmoothing k a b = k ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun x => (intervalStep a b x : ℂ)) := by
  funext s
  simp only [intervalSmoothing, convolution_def, ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

/-- The exact Fourier multiplier of the interval approximation. -/
theorem fourier_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b ξ : ℝ) :
    𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b) ξ =
      frequencyCutoff (ξ/T) * 𝓕 (fun x => (intervalStep a b x : ℂ)) ξ := by
  rw [intervalSmoothing_eq_convolution,
    Real.fourier_mul_convolution_eq (integrable_scaledKernel truncationKernel.integrable hT)
      (integrable_intervalStep a b), fourier_scaledKernel _ hT]
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f (ξ/T)) fourier_truncationKernel
  rw [SchwartzMap.fourier_coe] at h
  rw [h]

/-- No frequencies beyond the prescribed truncation height survive. -/
theorem fourier_intervalSmoothing_zero {T : ℝ} (hT : 0 < T) (a b ξ : ℝ)
    (hξ : T ≤ |ξ|) :
    𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b) ξ = 0 := by
  rw [fourier_intervalSmoothing hT, frequencyCutoff_zero, zero_mul]
  rw [abs_div, abs_of_pos hT]
  exact (le_div_iff₀ hT).mpr (by simpa using hξ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CutoffInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral representation of the interval cutoff

The same concrete smoothing used for the proved endpoint error is the
inverse Fourier integral of its compactly supported frequency multiplier.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform Convolution

namespace CubicFirstMoment

private theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) hf

theorem integrable_concrete_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    Integrable (intervalSmoothing (scaledKernel truncationKernel T) a b) := by
  rw [intervalSmoothing_eq_convolution]
  exact (integrable_scaledKernel truncationKernel.integrable hT).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_intervalStep a b)

theorem integrable_fourier_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    Integrable (𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b)) := by
  have hc := continuous_fourier_of_integrable (integrable_concrete_intervalSmoothing hT a b)
  have hs : HasCompactSupport (𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b)) := by
    apply HasCompactSupport.intro' (K := Set.Icc (-T) T) isCompact_Icc isClosed_Icc
    intro ξ hξ
    apply fourier_intervalSmoothing_zero hT
    simp only [Set.mem_Icc, not_and_or, not_le] at hξ
    rcases hξ with hξ | hξ
    · linarith [neg_abs_le ξ]
    · exact hξ.le.trans (le_abs_self ξ)
  exact hc.integrable_of_hasCompactSupport hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IntervalTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The interval Fourier multiplier

Evaluation of the interval transform gives the two endpoint terms divided
by frequency. The value at zero is the interval length, so there is no
singularity in the original multiplier.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform

namespace CubicFirstMoment

theorem fourier_intervalStep_eq_integral {a b : ℝ} (hab : a ≤ b) (ξ : ℝ) :
    𝓕 (fun x => (intervalStep a b x : ℂ)) ξ =
      ∫ x in a..b, Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun x : ℝ => Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) •
      (intervalStep a b x : ℂ)) = (Set.Icc a b).indicator
        (fun x => Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;>
      simp only [intervalStep, Set.indicator_apply, hx, ite_true, if_true, ite_false, if_false,
        Complex.ofReal_one, Complex.ofReal_zero, smul_eq_mul, mul_one, mul_zero]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

theorem fourier_intervalStep_nonzero {a b ξ : ℝ} (hab : a ≤ b) (hξ : ξ ≠ 0) :
    𝓕 (fun x => (intervalStep a b x : ℂ)) ξ =
      (Complex.exp ((-2 * Real.pi * b * ξ : ℝ) * Complex.I) -
        Complex.exp ((-2 * Real.pi * a * ξ : ℝ) * Complex.I)) /
          ((-2 * Real.pi * ξ : ℝ) * Complex.I) := by
  rw [fourier_intervalStep_eq_integral hab]
  have hc : ((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) Real.pi_ne_zero) hξ
  have he : (fun x : ℝ => Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I)) =
      (fun x : ℝ => Complex.exp (((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I * x)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex hc]
  congr 2 <;> congr 1 <;> push_cast <;> ring

/-- The multiplier for the dyadic interval [1,2], at every nonzero frequency. -/
theorem dyadic_interval_multiplier {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) ξ =
      (1 - Complex.exp ((-2 * Real.pi * Real.log 2 * ξ : ℝ) * Complex.I)) /
        ((2 * Real.pi * ξ : ℝ) * Complex.I) := by
  rw [fourier_intervalStep_nonzero (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hξ]
  simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero]
  have hneg : ((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I =
      -(((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [hneg]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBilinearMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of the actual varying outer weights in a
finite bilinear Gauss sum. All integrability follows from smooth support. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma metaplectic_mellin_term_integrable (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {V x : ℝ} (hV : 0 < V) (_hx : 0 < x) (a : ℂ) :
    Integrable (fun t : ℝ => zeroLineMellinWeight W V t*(a*mellinPhase (-t) x)) := by
  apply (zeroLineMellinWeight_integrable W hW hpos hsm hV).mul_bdd
    (c := ‖a‖)
  · have hc : Continuous (fun t : ℝ => a*mellinPhase (-t) x) := by
      unfold mellinPhase
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards with t
    simp [mellinPhase,Complex.norm_exp]

lemma metaplectic_mellin_term (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {V x : ℝ} (hV : 0 < V) (hx : 0 < x) (a : ℂ) :
    a*W (x/V) = ∫ t : ℝ, zeroLineMellinWeight W V t*(a*mellinPhase (-t) x) := by
  have h := smooth_mellin_finite (fun _ : Unit => a) (fun _ : Unit => x)
    (fun _ => hx) W hW hpos hsm 0 hV
  simp only [Fintype.sum_unique,Complex.ofReal_zero,zero_add] at h
  rw [h,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [mellinPhase_eq_cpow hx]
  have he : ((-t:ℝ):ℂ)*Complex.I = -((t:ℂ)*Complex.I) := by push_cast; ring
  rw [he]
  unfold zeroLineMellinWeight
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OverlapScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary powers and logarithmic absorption for model overlap. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma overlap_power_log_saving {c : ℝ} (hc : 0 < c) (a k : ℕ) :
    ∀ᶠ L : ℝ in atTop, (1+Real.log L)^a/L^c ≤ 1/(1+Real.log L)^(2*k) := by
  filter_upwards [negative_power_log_saving hc (a+2*k),eventually_ge_atTop (1:ℝ)] with L h hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL]
  calc
    _ = (1+Real.log L)^a*L^(-c) := by rw [Real.rpow_neg hLp.le]; ring
    _ ≤ (1+Real.log L)^a*(1/(1+Real.log L)^(a+2*k)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hz.le _)
    _ = _ := by rw [pow_add]; field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularGroupedPrimeHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The height mean for the two actual independent prime convolutions.
This supplies the complementary Mellin-frequency estimate after grouping. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem angular_full_prime_product_height_bilinear
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
    (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
    (hBhi : ∀ r i x, R < x → WB r i x = 0) (k : ℕ) :
    ∃ (η σ : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (eA eB : Eisenstein) (u T : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/4) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      eB ≠ 0 → norm eB ≤ (LB r)^σ →
      (1+Real.log (LB r))^m ≤ T → T ≤ (LB r)^(7/20:ℝ) → |u| ≤ (LB r)^(7/20:ℝ) →
      dyadicHeightMean (fun t =>
        ‖∑ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
          ∑ y ∈ fullSquarefreePrimeSupport R (WB r) XB eB,
            fullPrimeCoefficient R (WA r) XA x*fullPrimeCoefficient R (WB r) XB y*
              gauss (x*y)*theta ℓ (x*y)*normTwist (u+t) (x*y)‖) T ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨CA,d,hCA,henergy⟩ := logarithmic_full_coefficient_energy hWA hR hAlo hAhi
  have hM : 0 ≤ CA*2^d := by positivity
  obtain ⟨η,σ,hη,hη1,hσ,hbound⟩ := angular_rough_prime_height_bilinear ℓ
    (γ := γ) (ι := ι) (Q := R^Fintype.card κ)
    hpub hHuxley hperiod hMV hC hc hc1 hR hM hGI hGQ k d
  obtain ⟨G,K,B₀,m,hK,hbound⟩ := hbound LB WB hLB hWB hBlo hBhi
  refine ⟨η,σ,G,K,B₀,m,hη,hη1,hσ,hK,?_⟩
  intro r XA XB eA eB u T hT hprodA hprodB hXA hXB hAlow hAhigh he heN hTlow hThi hu
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hBp : 0 < LB r := zero_lt_one.trans_le (hLB r)
  have hlogB : 0 ≤ Real.log (LB r) := Real.log_nonneg (hLB r)
  have hpow : 1 ≤ (1+Real.log (LB r))^G := one_le_pow₀ (by linarith)
  have hAB : LA r ≤ (LB r)^2 := hAhigh.trans (div_le_self (sq_nonneg _) hpow)
  have hlogA : 1+Real.log (LA r) ≤ 2*(1+Real.log (LB r)) := by
    have hh := Real.log_le_log hAp hAB
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hα : (∑ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
      ‖angularHeightPrimeCoefficient ℓ R (WA r) XA x‖^2) ≤
        (CA*2^d)*LA r*(1+Real.log (LB r))^d := by
    rw [angularHeightPrimeCoefficient_energy]
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _))
    apply (henergy r XA (hLA r) hXA hprodA).trans
    calc
      _ ≤ CA*LA r*(2*(1+Real.log (LB r)))^d :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith [Real.log_nonneg (hLA r)]) hlogA d)
          (mul_nonneg hCA hAp.le)
      _ = _ := by rw [mul_pow]; ring
  have hP : ∀ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
      primary x ∧ norm x/LA r ∈ Set.Icc 1 (R^Fintype.card κ) := by
    intro x hx
    have hn := fullPrimeProduct_norm_bounds R (WA r) XA
      (fun i => zero_lt_one.trans_le (hXA i)) (hAlo r) (hAhi r) (Finset.mem_filter.mp hx).1
    rw [hprodA] at hn
    exact ⟨(fullSquarefreePrimeSupport_primary R (WA r) XA eA hx).1,
      (le_div_iff₀ hAp).mpr (by simpa only [one_mul] using hn.1),
      (div_le_iff₀ hAp).mpr hn.2⟩
  have hres := hbound r XB (LA r) eB u T
    (fullSquarefreePrimeSupport R (WA r) XA eA) (angularHeightPrimeCoefficient ℓ R (WA r) XA)
    hT hprodB hXB hAlow hAhigh he heN hTlow hThi hu hP hα
  simpa only [angularHeightPrimeCoefficient,theta_mul,mul_assoc,mul_left_comm,mul_comm] using hres

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

lemma fullPrimeCoefficient_l1_unit {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hW : ∀ i x, ‖W i x‖ ≤ 1) (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖) ≤
      primeCoefficientMassConstant R (Fintype.card ι)*(∏ i, X i) := by
  have hb (b : Eisenstein) : ‖fullPrimeCoefficient R W X b‖ ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ) := by
    simpa using fullPrimeCoefficient_norm_bound R W X (fun _ => 1)
      (fun _ => by norm_num) hW b
  calc
    _ ≤ ∑ _b ∈ fullSquarefreePrimeSupport R W X e,
        (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) := Finset.sum_le_sum (fun b _ => hb b)
    _ = ((fullSquarefreePrimeSupport R W X e).card:ℝ)*
        (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) := by simp
    _ ≤ (18*(R^Fintype.card ι*(∏ i, X i)))*
        (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) :=
      mul_le_mul_of_nonneg_right (fullPrimeSupport_card_bound hR W X hX hlo hhi e) (by positivity)
    _ = _ := by unfold primeCoefficientMassConstant; ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ZeroMellinDecay
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform decay in the total-product scale on the zero Mellin line. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma continuous_norm_zeroLineMellinWeight (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) {X : ℝ} (hX : 0 < X) :
    Continuous (fun t => ‖zeroLineMellinWeight W X t‖) := by
  have he : (fun t => ‖zeroLineMellinWeight W X t‖) =
      fun t => (1/(2*Real.pi))*‖mellinVerticalSchwartz W hW hpos hsm 0 t‖ := by
    funext t
    rw [zeroLineMellinWeight_norm W hX,mellinVerticalSchwartz_apply]
    simp only [Complex.ofReal_zero,zero_add]
  rw [he]
  exact continuous_const.mul (mellinVerticalSchwartz W hW hpos hsm 0).continuous.norm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailMellinMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full Mellin envelope preserves a translated height mean.
Only a bounded shift range is needed; the complement uses an actual moment
of the smooth Mellin weight and the coarse polynomial bound. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem complex_mellin_height_mean {P F w : ℝ → ℂ}
    (hP : Continuous P) (hF : Continuous F) (hw : Integrable w)
    (hwn : Continuous (fun s => ‖w s‖))
    (he : ∀ t, F t = ∫ s : ℝ, w s*P (t-s))
    {M B S T : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hS : 0 < S) (hT : 0 < T)
    (hbound : ∀ t, ‖P t‖ ≤ M) (n : ℕ)
    (hmoment : Integrable (fun s : ℝ => |s|^n*‖w s‖))
    (hsmall : ∀ s, |s| ≤ S → dyadicHeightMean (fun t => ‖P (t+s)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖F t‖) T ≤
      B*(∫ s : ℝ, ‖w s‖)+(2*M)/S^n*(∫ s : ℝ, |s|^n*‖w s‖) := by
  let f := fun s => ‖w (-s)‖
  let G := fun t => ‖P t‖
  have hf : Continuous f := hwn.comp continuous_neg
  have hfi : Integrable f := hw.norm.comp_neg
  have hG : Continuous G := hP.norm
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    rw [Real.norm_of_nonneg (_root_.norm_nonneg _)]
    exact hbound t
  have hconv : Continuous (fun t => ∫ s : ℝ, f s*G (t+0+s)) :=
    continuous_height_convolution hf hfi hG hGb 0
  have hm : Integrable (fun s : ℝ => ‖s‖^n*f s) := by
    simpa only [f,Real.norm_eq_abs,abs_neg] using hmoment.comp_neg
  have hmajor (t : ℝ) : ‖F t‖ ≤ ∫ s : ℝ, f s*G (t+0+s) := by
    rw [he t]
    calc
      _ ≤ ∫ s : ℝ, ‖w s*P (t-s)‖ := norm_integral_le_integral_norm _
      _ = ∫ s : ℝ, f s*G (t+0+s) := by
        rw [←integral_neg_eq_self (fun s : ℝ => ‖w s*P (t-s)‖) volume]
        simp only [f,G,norm_mul,sub_neg_eq_add,add_zero]
  have hc := dyadicHeightMean_convolution_window hf hfi (fun _ => _root_.norm_nonneg _)
    hG hM hB hS hT hGb 0 n hm (fun s hs => by
      simpa only [G,add_zero] using hsmall s (by simpa only [Real.norm_eq_abs] using hs))
  have hzero : (∫ s : ℝ, f s) = ∫ s : ℝ, ‖w s‖ := by
    simpa only [f] using integral_neg_eq_self (fun s : ℝ => ‖w s‖) volume
  have hn : (∫ s : ℝ, ‖s‖^n*f s) = ∫ s : ℝ, |s|^n*‖w s‖ := by
    simpa only [f,Real.norm_eq_abs,abs_neg] using
      integral_neg_eq_self (fun s : ℝ => |s|^n*‖w s‖) volume
  exact (dyadicHeightMean_mono hF.norm hconv hT (fun t _ => hmajor t)).trans
    (by simpa only [hzero,hn] using hc)

theorem zeroLineMellin_height_mean (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) {P F : ℝ → ℂ} (hP : Continuous P) (hF : Continuous F)
    (he : ∀ t, F t = ∫ s : ℝ, zeroLineMellinWeight W X s*P (t-s))
    {M B S T : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hS : 0 < S) (hT : 0 < T)
    (hbound : ∀ t, ‖P t‖ ≤ M) (n : ℕ)
    (hsmall : ∀ s, |s| ≤ S → dyadicHeightMean (fun t => ‖P (t+s)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖F t‖) T ≤
      B*zeroLineMellinMass W+(2*M)/S^n*zeroLineMellinMoment W n := by
  have hb := complex_mellin_height_mean hP hF
    (zeroLineMellinWeight_integrable W hW hpos hsm hX)
    (continuous_norm_zeroLineMellinWeight W hW hpos hsm hX) he hM hB hS hT hbound n
    (zeroLineMellinWeight_moment_integrable W hW hpos hsm hX n) hsmall
  rw [zeroLineMellinWeight_mass W hX,zeroLineMellinWeight_moment W hX n] at hb
  exact hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailProductMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-line Mellin separation for the original Gauss polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem product_gauss_mellin (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (u : ℝ) :
    productGaussSmoothed A B α β ℓ W X u =
      ∫ τ : ℝ, zeroLineMellinWeight W X τ*productGaussPolynomial A B α β ℓ (u-τ) := by
  let c := fun a b => α a*β b*theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b)
  let f := fun a b τ => zeroLineMellinWeight W X τ*(c a b*mellinPhase (-τ) (norm (a*b)))
  have hp (a : Eisenstein) (ha : a ∈ A) (b : Eisenstein) (hb : b ∈ B) :
      0 < norm (a*b) := norm_pos_of_ne_zero
        (mul_ne_zero (primary_ne_zero (hA a ha)) (primary_ne_zero (hB b hb)))
  have hi (a : Eisenstein) (ha : a ∈ A) (b : Eisenstein) (hb : b ∈ B) :
      Integrable (f a b) := metaplectic_mellin_term_integrable W hW hpos hsm hX (hp a ha b hb) (c a b)
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, ∫ τ : ℝ, f a b τ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact metaplectic_mellin_term W hW hpos hsm hX (hp a ha b hb) (c a b)
    _ = ∫ τ : ℝ, ∑ a ∈ A, ∑ b ∈ B, f a b τ := by
      rw [integral_finsetSum A (fun a ha => integrable_finsetSum B (hi a ha))]
      apply Finset.sum_congr rfl
      intro a ha
      exact (integral_finsetSum B (hi a ha)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [productGaussPolynomial,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [f,c]
      rw [sub_eq_add_neg,normTwist_eq_mellinPhase,normTwist_eq_mellinPhase,mellinPhase_add_height]
      ring

lemma productGaussPolynomial_continuous (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) : Continuous (productGaussPolynomial A B α β ℓ) := by
  unfold productGaussPolynomial normTwist
  fun_prop

lemma productGaussSmoothed_continuous (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) :
    Continuous (productGaussSmoothed A B α β ℓ W X) := by
  unfold productGaussSmoothed normTwist
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeProductPolynomialBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal angular Gauss product and its coefficient-mass bound. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma fullAngularPrimeProductGauss_bound (ℓ : ℤ) {R : ℝ} (hR : 0 ≤ R)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hWA : ∀ i x, ‖WA i x‖ ≤ 1) (hWB : ∀ i x, ‖WB i x‖ ≤ 1) (u : ℝ) :
    ‖fullAngularPrimeProductGauss ℓ R WA WB XA XB u‖ ≤
      (primeCoefficientMassConstant R (Fintype.card κ)*
        primeCoefficientMassConstant R (Fintype.card ι))*((∏ i, XA i)*(∏ i, XB i)) := by
  have hF (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R WA XA 1)
      (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R WB XB 1) :
      ‖theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b)‖ ≤ 1 := by
    have hn : a*b ≠ 0 := mul_ne_zero
      (primary_ne_zero (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1)
      (primary_ne_zero (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
    simp only [norm_mul,norm_theta hn,norm_normTwist,one_mul,mul_one]
    exact norm_gauss_le_one (primary_mul (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1
      (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
  have h := fullPrimeProduct_weighted_bound R WA WB XA XB
    (fun a b => theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b)) hF
  have hsame : (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
      ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
        fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*
          (theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b))) = fullAngularPrimeProductGauss ℓ R WA WB XA XB u := by
    simp only [fullAngularPrimeProductGauss,productGaussPolynomial,mul_assoc]
  rw [hsame,mul_one] at h
  apply h.trans
  apply (mul_le_mul (fullPrimeCoefficient_l1_unit hR WA XA hXA hAlo hAhi hWA 1)
    (fullPrimeCoefficient_l1_unit hR WB XB hXB hBlo hBhi hWB 1)
    (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))
    (by
      unfold primeCoefficientMassConstant
      exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => (hXA i).le)))).trans_eq
  ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailProductMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded-shift mean for the unsmoothed Gauss polynomial suffices
for its actual product envelope. All complementary Mellin frequencies are
paid for by an integrable moment, with no frequency discarded. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellinMoment_nonneg (W : ℝ → ℂ) (n : ℕ) :
    0 ≤ zeroLineMellinMoment W n := by
  unfold zeroLineMellinMoment
  positivity

theorem productGaussSmoothed_height_mean (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X M B V T : ℝ} (hX : 0 < X) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hV : 0 < V) (hT : 0 < T)
    (hbound : ∀ u, ‖productGaussPolynomial P S α β ℓ u‖ ≤ M) (n : ℕ)
    (hsmall : ∀ u, |u| ≤ V →
      dyadicHeightMean (fun t => ‖productGaussPolynomial P S α β ℓ (t+u)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖productGaussSmoothed P S α β ℓ W X t‖) T ≤
      B*zeroLineMellinMass W+(2*M)/V^n*zeroLineMellinMoment W n := by
  exact zeroLineMellin_height_mean W hW hpos hsm hX
    (productGaussPolynomial_continuous P S α β ℓ)
    (productGaussSmoothed_continuous P S α β ℓ W X)
    (fun t => product_gauss_mellin P S α β hP hS ℓ W hW hpos hsm hX t)
    hM hB hV hT hbound n hsmall

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeTailProductMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Mellin envelope for the actual fixed-angular prime polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem angular_fullPrimeProductSmoothed_height_mean (ℓ : ℤ) {R : ℝ} (hR : 0 ≤ R)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hWA : ∀ i x, ‖WA i x‖ ≤ 1) (hWB : ∀ i x, ‖WB i x‖ ≤ 1)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X E V T : ℝ} (hX : 0 < X) (hE : 0 ≤ E)
    (hV : 0 < V) (hT : 0 < T) (n : ℕ)
    (hsmall : ∀ u, |u| ≤ V →
      dyadicHeightMean (fun t => ‖fullAngularPrimeProductGauss ℓ R WA WB XA XB (u+t)‖) T ≤ E) :
    dyadicHeightMean (fun t => ‖productGaussSmoothed
      (fullSquarefreePrimeSupport R WA XA 1) (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) ℓ W X t‖) T ≤
      E*zeroLineMellinMass W+
        (2*(primeCoefficientMassConstant R (Fintype.card κ)*
          primeCoefficientMassConstant R (Fintype.card ι)*(∏ i, XA i)*(∏ i, XB i)))/V^n*
            zeroLineMellinMoment W n := by
  have he (u : ℝ) : productGaussPolynomial
      (fullSquarefreePrimeSupport R WA XA 1) (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) ℓ u =
      fullAngularPrimeProductGauss ℓ R WA WB XA XB u := by
    rfl
  have hpA : 0 ≤ ∏ i, XA i := (Finset.prod_pos (fun i _ => hXA i)).le
  have hpB : 0 ≤ ∏ i, XB i := (Finset.prod_pos (fun i _ => hXB i)).le
  apply productGaussSmoothed_height_mean _ _ _ _
    (fun a ha => (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1)
    (fun b hb => (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
    ℓ W hW hpos hsm hX (by unfold primeCoefficientMassConstant; positivity) hE hV hT _ n _
  · intro u
    rw [he]
    simpa only [mul_assoc] using fullAngularPrimeProductGauss_bound ℓ hR WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi hWA hWB u
  · intro u hu
    simp_rw [he]
    simpa only [add_comm] using hsmall u hu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailMellinScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eight Mellin moments at B^(1/4) absorb the coarse product mass
throughout A <= B². The remaining factor B^(-1) pays for any fixed log. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma primeTail_mellin_error_scale {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B)
    (hAB : A ≤ B^2) :
    A*B/(B^(1/4:ℝ))^8 ≤ A^(5/6:ℝ)*B^(5/6:ℝ)/B := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hVp : 0 < A*B := mul_pos hA hBp
  have hV : A*B ≤ B^3 := by nlinarith [mul_le_mul_of_nonneg_right hAB hBp.le]
  have hroot : (A*B)^(1/6:ℝ) ≤ B := by
    calc
      _ ≤ (B^3)^(1/6:ℝ) := Real.rpow_le_rpow hVp.le hV (by norm_num)
      _ = B^(1/2:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul hBp.le]; norm_num
      _ ≤ B^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
      _ = B := Real.rpow_one B
  have hs : (B^(1/4:ℝ))^8 = B^2 := by
    rw [←Real.rpow_mul_natCast hBp.le]
    norm_num
  rw [hs]
  apply (div_le_div_iff₀ (sq_pos_of_pos hBp) hBp).mpr
  have he : A*B = (A*B)^(5/6:ℝ)*(A*B)^(1/6:ℝ) := by
    rw [←Real.rpow_add hVp]
    norm_num
  have hh := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (A*B)^(5/6:ℝ)*B by positivity)
  rw [Real.mul_rpow hA.le hBp.le] at hh
  calc
    A*B*B = ((A*B)^(5/6:ℝ)*(A*B)^(1/6:ℝ))*B := by rw [←he]
    _ = (A^(5/6:ℝ)*B^(5/6:ℝ)*B)*(A*B)^(1/6:ℝ) := by
      rw [Real.mul_rpow hA.le hBp.le]
      ring
    _ ≤ (A^(5/6:ℝ)*B^(5/6:ℝ)*B)*B := hh
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeTailHeckeMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published Hecke height mean applied through the full original
product envelope. The bounded shift condition is discharged using eight
Mellin moments and the actual coarse prime-convolution bound. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem angular_full_prime_product_smoothed_height
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
    (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
    (hBhi : ∀ r i x, R < x → WB r i x = 0)
    (hWAone : ∀ r i x, ‖WA r i x‖ ≤ 1) (hWBone : ∀ r i x, ‖WB r i x‖ ≤ 1)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (k : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (X T : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/4) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      0 < X →
      (1+Real.log (LB r))^m ≤ T → T ≤ (LB r)^(7/20:ℝ) →
      dyadicHeightMean (fun t => ‖productGaussSmoothed
        (fullSquarefreePrimeSupport R (WA r) XA 1)
        (fullSquarefreePrimeSupport R (WB r) XB 1)
        (fullPrimeCoefficient R (WA r) XA) (fullPrimeCoefficient R (WB r) XB)
        ℓ W X t‖) T ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨η,σ,G,K,B₀,m,hη,hηone,hσ,hK,hmean⟩ := angular_full_prime_product_height_bilinear ℓ
    hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ LA LB WA WB hLA hLB hWA hWB
    hAlo hAhi hBlo hBhi k
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp
    (overlap_power_log_saving (by norm_num : (0:ℝ) < 1) k 0)
  let M := primeCoefficientMassConstant R (Fintype.card κ)*
    primeCoefficientMassConstant R (Fintype.card ι)
  have hM : 0 ≤ M := by dsimp [M,primeCoefficientMassConstant]; positivity
  let K' := K*zeroLineMellinMass W+2*M*zeroLineMellinMoment W 8+1
  have hmass := zeroLineMellinMass_nonneg W
  have hmom := zeroLineMellinMoment_nonneg W 8
  refine ⟨η,G,K',max B₀ B₁,m,hη,hηone,by dsimp [K']; positivity,?_⟩
  intro r XA XB X T hB hprodA hprodB hXA hXB hAlow hAhigh hX hT hThi
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hBp : 0 < LB r := zero_lt_one.trans_le (hLB r)
  have hL : 0 < 1+Real.log (LB r) := by linarith [Real.log_nonneg (hLB r)]
  have hLone : 1 ≤ 1+Real.log (LB r) := by linarith [Real.log_nonneg (hLB r)]
  have hAB : LA r ≤ (LB r)^2 :=
    hAhigh.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hLone))
  have hTpos : 0 < T := (pow_pos hL m).trans_le hT
  have hsmall (u : ℝ) (hu : |u| ≤ (LB r)^(1/4:ℝ)) :
      dyadicHeightMean (fun t => ‖fullAngularPrimeProductGauss ℓ R (WA r) (WB r) XA XB (u+t)‖) T ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
    simpa only [fullAngularPrimeProductGauss,productGaussPolynomial,mul_assoc,mul_left_comm,mul_comm]
      using hmean r XA XB 1 1 u T ((le_max_left _ _).trans hB) hprodA hprodB hXA hXB
      hAlow hAhigh one_ne_zero (by simp; exact Real.one_le_rpow (hLB r) hσ.le) hT hThi
      (hu.trans (Real.rpow_le_rpow_of_exponent_le (hLB r) (by norm_num)))
  have hb := angular_fullPrimeProductSmoothed_height_mean ℓ (zero_le_one.trans hR) (WA r) (WB r) XA XB
    (fun i => zero_lt_one.trans_le (hXA i))
    (fun i => lt_trans (Real.rpow_pos_of_pos (by linarith [hLB r] : 0 < 2*LB r) c) (hXB i))
    (hAlo r) (hAhi r) (hBlo r) (hBhi r) (hWAone r) (hWBone r)
    W hW hpos hsm hX (by positivity) (Real.rpow_pos_of_pos hBp _) hTpos 8 hsmall
  rw [hprodA,hprodB] at hb
  have hlog : (1+Real.log (LB r))^k ≤ LB r := by
    have hh := hB₁ (LB r) ((le_max_right _ _).trans hB)
    simp only [Real.rpow_one,Nat.mul_zero,pow_zero,div_one] at hh
    exact (div_le_one hBp).mp hh
  have he := primeTail_mellin_error_scale hAp (hLB r) hAB
  have he' : LA r*LB r/((LB r)^(1/4:ℝ))^8 ≤
      (LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k :=
    he.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hL k) hlog)
  have herr : (2*(M*LA r*LB r))/((LB r)^(1/4:ℝ))^8*zeroLineMellinMoment W 8 ≤
      (2*M*zeroLineMellinMoment W 8)*
        ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) := by
    calc
      _ = (2*M*zeroLineMellinMoment W 8)*
          (LA r*LB r/((LB r)^(1/4:ℝ))^8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he' (by positivity)
  apply hb.trans
  change (K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k)*zeroLineMellinMass W+
    (2*(M*LA r*LB r))/((LB r)^(1/4:ℝ))^8*zeroLineMellinMoment W 8 ≤ _
  calc
    _ ≤ (K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k)*zeroLineMellinMass W+
        (2*M*zeroLineMellinMoment W 8)*
          ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) :=
      add_le_add le_rfl herr
    _ = (K*zeroLineMellinMass W+2*M*zeroLineMellinMoment W 8)*
        ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) := by ring
    _ ≤ K'*((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) :=
      mul_le_mul_of_nonneg_right (by dsimp [K']; linarith) (by positivity)
    _ = _ := by ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightPolynomialIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete sharp-cutoff smoothing in the manuscript's height variable.
The Fourier convention contributes the explicit Jacobian `1 / (2π)`.
All finite sums below retain their original coefficients and support. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

lemma cutoffHeightMultiplier_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (cutoffHeightMultiplier T) := by
  have h := (integrable_fourier_intervalSmoothing hT 0 (Real.log 2)).comp_div
    (show 2*Real.pi ≠ 0 by positivity)
  change Integrable (fun t => frequencyCutoff ((t/(2*Real.pi))/T) *
    𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) (t/(2*Real.pi)))
  simpa only [fourier_intervalSmoothing hT] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth height windows with ratio 3/2. Their support lies in [T,2T]
in absolute value, exactly the range of the proved bilinear estimates.
The finite telescoping identity keeps the actual truncation multiplier. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma heightWindow_norm_le (T t : ℝ) : ‖heightWindow T t‖ ≤ 1 := by
  rw [heightWindow, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [heightPartitionBump.nonneg (x := t/((3/2)*T)),
    heightPartitionBump.le_one (x := t/((3/2)*T)),
    heightPartitionBump.nonneg (x := t/T), heightPartitionBump.le_one (x := t/T)]

lemma integrable_cutoffHeightMultiplier_window {S : ℝ} (hS : 0 < S) (T : ℝ) :
    Integrable (fun t => cutoffHeightMultiplier S t*heightWindow T t) :=
  (cutoffHeightMultiplier_integrable hS).mul_bdd
    (heightWindow_smooth T).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (heightWindow_norm_le T))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWindowCount
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite height partition. Every nonzero window lies below
the Fourier cap, and the number of windows costs only one logarithm. -/
noncomputable section
namespace CubicFirstMoment

lemma heightWindowCount_scale_bounds {S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    {j : ℕ} (hj : j < heightWindowCount S T) :
    T ≤ T*(3/2:ℝ)^j ∧ T*(3/2:ℝ)^j < 2*Real.pi*S := by
  have hr : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have hj' : (j:ℝ) < Real.log ((2*Real.pi*S)/T)/Real.log (3/2:ℝ) := Nat.lt_ceil.mp hj
  have hlog : Real.log ((3/2:ℝ)^j) < Real.log ((2*Real.pi*S)/T) := by
    rw [Real.log_pow]
    exact (lt_div_iff₀ hr).mp hj'
  have hb := (Real.log_lt_log_iff (by positivity : 0 < (3/2:ℝ)^j)
    (div_pos (by positivity) hT)).mp hlog
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2)) hT.le
  · simpa only [mul_comm] using (lt_div_iff₀ hT).mp hb

theorem heightWindowCount_log_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ S T : ℝ, 1 ≤ S → 1 ≤ T →
      (heightWindowCount S T:ℝ) ≤ K*(1+Real.log S) := by
  let r := Real.log (3/2:ℝ)
  let a := 1+Real.log (2*Real.pi)/r
  let b := 1/r
  have hr : 0 < r := Real.log_pos (by norm_num)
  have hc : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have ha : 0 ≤ a := by
    have hc' := Real.log_nonneg hc
    dsimp [a]
    positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨a+b, by linarith, ?_⟩
  intro S T hS hT
  have hSp : 0 < S := zero_lt_one.trans_le hS
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hcap : 1 ≤ 2*Real.pi*S := by nlinarith
  have hmono : heightWindowCount S T ≤ ⌈Real.log (2*Real.pi*S)/r⌉₊ := by
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hr.le
    rw [Real.log_div (by positivity : 2*Real.pi*S ≠ 0) hTp.ne']
    linarith [Real.log_nonneg hT]
  have hceil := (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hcap) hr.le)).le
  have hstart := (Nat.cast_le.mpr hmono).trans hceil
  rw [Real.log_mul (by positivity : 2*Real.pi ≠ 0) hSp.ne', add_div] at hstart
  have he : Real.log (2*Real.pi)/r+Real.log S/r+1 = a+b*Real.log S := by
    dsimp [a,b]
    ring
  apply hstart.trans
  rw [he]
  nlinarith [mul_nonneg ha hlogS]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWindowSum
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual finite ratio-3/2 height windows costs one logarithm. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem height_window_sum_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (H T E : ℝ) (f : ℝ → ℂ),
      1 ≤ H → 1 ≤ T → 0 ≤ E →
      (∀ t, T ≤ t → t < 2*Real.pi*H → ‖f t‖ ≤ E) →
      ‖∑ j ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^j)‖ ≤
        K*(1+Real.log H)*E := by
  obtain ⟨K,hK,hcount⟩ := heightWindowCount_log_bound
  refine ⟨K,hK,?_⟩
  intro H T E f hH hT hE hf
  calc
    _ ≤ ∑ j ∈ Finset.range (heightWindowCount H T), ‖f (T*(3/2:ℝ)^j)‖ :=
      norm_sum_le _ _
    _ ≤ (heightWindowCount H T:ℝ)*E := by
      have hb (j : ℕ) (hj : j ∈ Finset.range (heightWindowCount H T)) :
          ‖f (T*(3/2:ℝ)^j)‖ ≤ E := by
        have hs := heightWindowCount_scale_bounds (zero_lt_one.trans_le hH)
          (zero_lt_one.trans_le hT) (Finset.mem_range.mp hj)
        exact hf _ hs.1 hs.2
      simpa using Finset.sum_le_sum hb
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcount H T hH hT) hE

theorem height_window_sum_log_saving :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (H T Z B K : ℝ) (j : ℕ) (f : ℝ → ℂ),
      1 ≤ H → 1 ≤ T → 1 ≤ Z → H ≤ Z^3 → 0 ≤ B → 0 ≤ K →
      (∀ t, T ≤ t → t < 2*Real.pi*H →
        ‖f t‖ ≤ K*B/(1+Real.log Z)^(j+1)) →
      ‖∑ i ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^i)‖ ≤
        K₀*K*B/(1+Real.log Z)^j := by
  obtain ⟨K₀,hK₀,hbound⟩ := height_window_sum_bound
  refine ⟨3*K₀,by positivity,?_⟩
  intro H T Z B K j f hH hT hZ hHZ hB hK hf
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ]
  have hlog : 1+Real.log H ≤ 3*(1+Real.log Z) := by
    have hh := Real.log_le_log (zero_lt_one.trans_le hH) hHZ
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  apply (hbound H T (K*B/(1+Real.log Z)^(j+1)) f hH hT (by positivity) hf).trans
  calc
    _ ≤ K₀*(3*(1+Real.log Z))*(K*B/(1+Real.log Z)^(j+1)) := by gcongr
    _ = (3*K₀)*K*B/(1+Real.log Z)^j := by
      rw [pow_succ]
      field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDetectorCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth cutoff for the exact prime detector. -/
noncomputable section
open Filter
open scoped ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeDetectorCutoff_nonneg (x : ℝ) : 0 ≤ primeDetectorCutoff x :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

lemma primeDetectorCutoff_le_one (x : ℝ) : primeDetectorCutoff x ≤ 1 := by
  unfold primeDetectorCutoff
  linarith [Real.smoothTransition.nonneg (x-1)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightMultiplier
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint phases of the actual cutoff. On each smooth height
window the normalized reciprocal factor is uniformly bounded. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma frequencyCutoff_norm_le (x : ℝ) : ‖frequencyCutoff x‖ ≤ 1 := by
  rw [frequencyCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg frequencyBump.nonneg]
  exact frequencyBump.le_one

lemma cutoffHeightMultiplier_eq_endpoints (S : ℝ) {t : ℝ} (ht : t ≠ 0) :
    cutoffHeightMultiplier S t = frequencyCutoff ((t/(2*Real.pi))/S) *
      ((1-Complex.exp ((-Real.log 2*t : ℝ)*Complex.I))/((t:ℂ)*Complex.I)) := by
  rw [cutoffHeightMultiplier, dyadic_interval_multiplier
    (div_ne_zero ht (by positivity))]
  have he : -2*Real.pi*Real.log 2*(t/(2*Real.pi)) = -Real.log 2*t := by field_simp
  have hd : 2*Real.pi*(t/(2*Real.pi)) = t := by field_simp
  rw [he,hd]

lemma cutoffHeightMultiplier_norm_le (S : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ‖cutoffHeightMultiplier S t‖ ≤ 2/|t| := by
  rw [cutoffHeightMultiplier_eq_endpoints S ht, norm_mul]
  have hnum : ‖1-Complex.exp ((-Real.log 2*t : ℝ)*Complex.I)‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    simp only [norm_one, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_self, Real.exp_zero]
    norm_num
  calc
    _ ≤ 1*(2/|t|) := mul_le_mul (frequencyCutoff_norm_le _) (by
      simpa only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one] using div_le_div_of_nonneg_right hnum (abs_nonneg t))
      (by positivity) (by norm_num)
    _ = _ := one_mul _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Fourier height window is bounded by its two-sided mean,
including the reciprocal height normalization and both endpoint phases. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cutoffHeightWindow_integral_bound (f : ℝ → ℂ) (hf : Continuous f)
    (H X : ℝ) {T : ℝ} (hT : 0 < T) :
    ‖∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
      Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*f t‖ ≤
      2*dyadicHeightMean (fun t => ‖f t‖) T := by
  let w := fun t => cutoffHeightMultiplier H t*heightWindow T t*
    Complex.exp ((-Real.log X*t:ℝ)*Complex.I)
  have hs (t : ℝ) (ht : t ∉ dyadicHeightSupport T) : w t = 0 := by
    simp only [w,heightWindow_zero hT ht,mul_zero,zero_mul]
  have hb (t : ℝ) : ‖w t‖ ≤ 2/T := by
    by_cases ht : t ∈ dyadicHeightSupport T
    · have ha : T ≤ |t| := by
        rcases ht with ht | ht
        · exact ht.1.trans (le_abs_self t)
        · exact (by linarith [ht.2] : T ≤ -t).trans (neg_le_abs t)
      have hp : 0 < |t| := hT.trans_le ha
      simp only [w,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
      calc
        _ ≤ ‖cutoffHeightMultiplier H t‖*1 :=
          mul_le_mul_of_nonneg_left (heightWindow_norm_le T t) (_root_.norm_nonneg _)
        _ ≤ 2/|t| := by simpa only [mul_one] using cutoffHeightMultiplier_norm_le H (abs_pos.mp hp)
        _ ≤ 2/T := div_le_div_of_nonneg_left (by norm_num) hT ha
    · rw [hs t ht,norm_zero]
      positivity
  have he := dyadicWeightIntegral_bound f w hf hT (by positivity : 0 ≤ 2/T) hb hs
  change ‖∫ t : ℝ, w t*f t‖ ≤ _
  exact he.trans_eq (by field_simp)

lemma productGaussWindow_integral (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) {H : ℝ} (hH : 0 < H) (U X : ℝ) :
    productGaussWindow P S α β ℓ W H U X =
      ∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow U t*
        Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*
          productGaussSmoothed P S α β ℓ W X t := by
  let c := fun q : Eisenstein × Eisenstein =>
    α q.1*β q.2*theta ℓ (q.1*q.2)*gauss (q.1*q.2)*W (norm (q.1*q.2)/X)
  have he := height_norm_polynomial_integral (P.product S) c (fun q => q.1*q.2)
    (fun t => cutoffHeightMultiplier H t*heightWindow U t)
    (integrable_cutoffHeightMultiplier_window hH U) (Real.log X)
  simp only [Finset.product_eq_sprod,Finset.sum_product] at he
  calc
    _ = ∑ a ∈ P, ∑ b ∈ S, c (a,b)*
        heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow U t)
          (Real.log (norm (a*b))-Real.log X) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp [productGaussWindow,productGaussHeightWindowKernel,c]
      ring
    _ = _ := by
      rw [he]
      congr 1
      funext t
      simp only [productGaussSmoothed,Finset.mul_sum,c]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

lemma productGaussWindow_bound (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) {H U : ℝ} (hH : 0 < H) (hU : 0 < U) (X : ℝ) :
    ‖productGaussWindow P S α β ℓ W H U X‖ ≤
      2*dyadicHeightMean (fun t => ‖productGaussSmoothed P S α β ℓ W X t‖) U := by
  rw [productGaussWindow_integral P S α β ℓ W hH U X]
  exact cutoffHeightWindow_integral_bound _
    (productGaussSmoothed_continuous P S α β ℓ W X) H X hU

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeTailHeckeTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-envelope Hecke mean summed over the actual finite height tail. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem angular_full_prime_product_envelope_tail
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
    (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
    (hBhi : ∀ r i x, R < x → WB r i x = 0)
    (hWAone : ∀ r i x, ‖WA r i x‖ ≤ 1) (hWBone : ∀ r i x, ‖WB r i x‖ ≤ 1)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (k : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (X H T : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/4) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      0 < X →
      (1+Real.log (LB r))^m ≤ T → 1 ≤ H → H ≤ (LB r)^3 →
      2*Real.pi*H ≤ (LB r)^(7/20:ℝ) →
      ‖envelopeCutoffBilinearTail
        (fullSquarefreePrimeSupport R (WA r) XA 1)
        (fullSquarefreePrimeSupport R (WB r) XB 1)
        (fun a => theta ℓ a*fullPrimeCoefficient R (WA r) XA a)
        (fun b => theta ℓ b*fullPrimeCoefficient R (WB r) XB b)
        W H T X‖ ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨η,G,K,B₀,m,hη,hηone,hK,hmean⟩ := angular_full_prime_product_smoothed_height ℓ
    hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ LA LB WA WB hLA hLB hWA hWB
    hAlo hAhi hBlo hBhi hWAone hWBone W hW hpos hsm (k+1)
  obtain ⟨K₀,hK₀,hsum⟩ := height_window_sum_log_saving
  refine ⟨η,G,K₀*(2*K),B₀,m,hη,hηone,by positivity,?_⟩
  intro r XA XB X H T hB hprodA hprodB hXA hXB hAlow hAhigh hX hT hH hHB hHtop
  let P := fullSquarefreePrimeSupport R (WA r) XA 1
  let S := fullSquarefreePrimeSupport R (WB r) XB 1
  let α := fullPrimeCoefficient R (WA r) XA
  let β := fullPrimeCoefficient R (WB r) XB
  have hL1 : 1 ≤ 1+Real.log (LB r) := by linarith [Real.log_nonneg (hLB r)]
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hBp : 0 < LB r := zero_lt_one.trans_le (hLB r)
  have hT1 : 1 ≤ T := (one_le_pow₀ hL1).trans hT
  have hb (u : ℝ) (htu : T ≤ u) (huh : u < 2*Real.pi*H) :
      ‖productGaussWindow P S α β ℓ W H u X‖ ≤
        (2*K)*((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ))/(1+Real.log (LB r))^(k+1) := by
    have hu : 0 < u := zero_lt_one.trans_le (hT1.trans htu)
    apply (productGaussWindow_bound P S α β ℓ W (zero_lt_one.trans_le hH) hu X).trans
    have hm := hmean r XA XB X u hB hprodA hprodB hXA hXB hAlow hAhigh hX
      (hT.trans htu) (huh.le.trans hHtop)
    exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  have hs := hsum H T (LB r) ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)) (2*K) k
    (fun u => productGaussWindow P S α β ℓ W H u X) hH hT1 (hLB r) hHB
    (by positivity) (by positivity) hb
  have he : envelopeCutoffBilinearTail P S (fun a => theta ℓ a*α a)
      (fun b => theta ℓ b*β b) W H T X =
      ∑ v ∈ Finset.range (heightWindowCount H T),
        productGaussWindow P S α β ℓ W H (T*(3/2:ℝ)^v) X := by
    unfold envelopeCutoffBilinearTail productGaussWindow
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [productGaussHeightWindowKernel,theta_mul]
    ring
  change ‖envelopeCutoffBilinearTail P S (fun a => theta ℓ a*α a)
      (fun b => theta ℓ b*β b) W H T X‖ ≤ _
  rw [he]
  exact hs.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeSmoothWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The roughness transition in each actual semiprime norm piece belongs
to a single uniform smooth family. Capping its scale ratio at two is an
identity on the fixed norm support, so all logarithmic derivatives are
uniform even when the original ratio is unbounded. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma semiprimeSmoothWeight_high (r : ℝ) {x : ℝ} (hx : 2 < x) :
    semiprimeSmoothWeight r x = 0 := by
  rw [semiprimeSmoothWeight,normPartitionWeight_high hx,zero_mul]

lemma semiprimeSmoothWeight_norm (r x : ℝ) : ‖semiprimeSmoothWeight r x‖ ≤ 1 := by
  have hc : ‖1-(primeDetectorCutoff (r*x):ℂ)‖ ≤ 1 := by
    have he : (1-(primeDetectorCutoff (r*x):ℂ)) =
        ((1-primeDetectorCutoff (r*x):ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (sub_nonneg.mpr (primeDetectorCutoff_le_one _))]
    linarith [primeDetectorCutoff_nonneg (r*x)]
  rw [semiprimeSmoothWeight,norm_mul]
  exact (mul_le_mul (normPartitionWeight_norm x) hc (_root_.norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single uniform smooth family for the actual distinguished-prime
weights in each large-row norm piece. Both scale ratios are capped only
after proving that the cap leaves the weight unchanged. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma distinguishedSmoothWeight_low (r : ℝ × ℝ) {x : ℝ} (hx : x < 1) :
    distinguishedSmoothWeight r x = 0 := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_low _ hx,sub_self]

lemma distinguishedSmoothWeight_high (r : ℝ × ℝ) {x : ℝ} (hx : 2 < x) :
    distinguishedSmoothWeight r x = 0 := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_high _ hx,sub_self]

lemma distinguishedSmoothWeight_norm (r : ℝ × ℝ) (x : ℝ) :
    ‖distinguishedSmoothWeight r x‖ ≤ 1 := by
  have he : distinguishedSmoothWeight r x = normPartitionWeight x*
      ((primeDetectorCutoff (r.1*x)-primeDetectorCutoff (r.2*x):ℝ):ℂ) := by
    simp only [distinguishedSmoothWeight,semiprimeSmoothWeight,Complex.ofReal_sub]
    ring
  have hb : |primeDetectorCutoff (r.1*x)-primeDetectorCutoff (r.2*x)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [primeDetectorCutoff_nonneg (r.1*x),
      primeDetectorCutoff_nonneg (r.2*x),primeDetectorCutoff_le_one (r.1*x),
      primeDetectorCutoff_le_one (r.2*x)]
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (normPartitionWeight_norm x) hb (abs_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCoordinateWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual independently smoothed prime coordinates of a large row
belong to one uniform family, for every norm partition and roughness scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

lemma largeTupleCoordinateWeight_norm {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) (x : ℝ) :
    ‖largeTupleCoordinateWeight ξ X k a x‖ ≤ 1 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_norm _ x
  · exact semiprimeSmoothWeight_norm _ x

lemma largeTupleCoordinateWeight_low {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) {x : ℝ} (hx : x < 1) :
    largeTupleCoordinateWeight ξ X k a x = 0 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_low _ hx
  · exact semiprimeSmoothWeight_low _ hx

lemma largeTupleCoordinateWeight_high {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) {x : ℝ} (hx : 2 < x) :
    largeTupleCoordinateWeight ξ X k a x = 0 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_high _ hx
  · exact semiprimeSmoothWeight_high _ hx

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleRestrictedWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate weights restricted to either predicate in a fixed
partition of the tuple indices. This preserves the predicate-subtype
indexing in the exact finite convolution identity. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {i j : ℕ} (P : (Fin i ⊕ Fin j) → Prop) [DecidablePred P]

lemma largeTupleRestrictedLength_notMem (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) :
    largeTupleRestrictedLength (fun a => a ∉ s) z =
      largeTupleGroupLength (Finset.univ\s) z := by
  exact (Finset.prod_subtype (Finset.univ\s) (by simp)
    (fun a => largeTupleNormScale z.1.2 a)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeHeckeGroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Specialization of the full-envelope Hecke tail to the literal
independent coordinates supplied by a surviving prime tuple. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma envelopeCutoffBilinearTail_swap (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (W : ℝ → ℂ) (H T X : ℝ) :
    envelopeCutoffBilinearTail P S α β W H T X =
      envelopeCutoffBilinearTail S P β α W H T X := by
  unfold envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm b a]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTailPrimeHeckeGroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Specialization of the full-envelope Hecke tail to the literal
independent coordinates supplied by a surviving prime tuple. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_tailPrime_hecke_group_oai {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (k : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      B₀ ≤ B → (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      B^(1-η/16) ≤ A → A ≤ B^2/(1+Real.log B)^G →
      (1+Real.log B)^m ≤ T → 1 ≤ H → H ≤ B^3 → 2*Real.pi*H ≤ B^(7/20:ℝ) →
      ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (fun b => theta ℓ b*largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s b)
        (fun a => theta ℓ a*largeTupleOtherCoefficient ξ z.1.1 z.1.2 s a)
        primeProductEnvelope H T z.1.1‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨η,G,K,B₀,m,hη,hηone,hK,hbound⟩ := angular_full_prime_product_envelope_tail ℓ
    hpub hHuxley hperiod hMV hC (by positivity : (0:ℝ) < ξ/2)
    (by linarith : ξ/2 ≤ 1) (by norm_num : (1:ℝ) ≤ 2) hGI hGQ
    (largeTupleRestrictedLength (fun a => a ∉ s)) (largeTupleGroupLength s)
    (largeTupleRestrictedWeight (fun a => a ∉ s) ξ) (largeTupleGroupWeight ξ s)
    (largeTupleRestrictedLength_one (fun a => a ∉ s)) (largeTupleGroupLength_one s)
    (largeTupleRestrictedLogWeights (fun a => a ∉ s) ξ) (largeTupleGroupLogWeights ξ s)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z a x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 a x)
    (fun z a x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 a x)
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth k
  refine ⟨η,G,K,B₀,m,hη,hηone,hK,?_⟩
  intro z H T
  dsimp only
  intro hB hrough hAlow hAhigh hT hH hHcube hHtop
  have hb := hbound z
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale z.1.2 a)
    (fun a : s => largeTupleNormScale z.1.2 a) z.1.1 H T
  simp only [largeTupleRestrictedLength_notMem] at hb
  have hh := hb hB (largeTupleRestrictedLength_notMem s z)
    (Finset.prod_coe_sort s (fun a => largeTupleNormScale z.1.2 a))
    (fun a => z.property a) hrough
    ((Real.rpow_le_rpow_of_exponent_le (largeTupleGroupLength_one s z)
      (by linarith : 1-η/4 ≤ 1-η/16)).trans hAlow)
    hAhigh z.1.1.property hT hH hHcube hHtop
  rw [envelopeCutoffBilinearTail_swap]
  exact hh

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.angular_tailPrime_hecke_group_oai := @OAI.CubicFirstMoment.angular_tailPrime_hecke_group_oai
