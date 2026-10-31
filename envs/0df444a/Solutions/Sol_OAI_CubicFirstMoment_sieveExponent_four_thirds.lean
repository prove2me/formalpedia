-- Prove2me | solution 1 for OAI.CubicFirstMoment.sieveExponent_four_thirds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:57:55.132182+00:00
-- url     : https://prove2.me/submissions/6056bd4b-64f7-4e1b-9b13-86725cdc831d

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022
import Theorems.Thm_OAI_CubicFirstMoment_SieveExponent_recurrence

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

private lemma euclideanConj_norm {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    ‖euclideanConj v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, euclideanConj]

private lemma matrixHilbertOperator_conj {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (v : EuclideanSpace ℂ κ) :
    matrixHilbertOperator (A.map star) v =
      euclideanConj (matrixHilbertOperator A (euclideanConj v)) := by
  apply PiLp.ext
  intro i
  change (∑ j, star (A i j) * v j) = star (∑ j, A i j * star (v j))
  simp [star_sum, star_mul, mul_comm]

private lemma matrixHilbertOperator_conj_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) :
    ‖matrixHilbertOperator (A.map star)‖ ≤ ‖matrixHilbertOperator A‖ := by
  apply (ContinuousLinearMap.opNorm_le_iff (f := matrixHilbertOperator (A.map star))
    (_root_.norm_nonneg (matrixHilbertOperator A))).mpr
  intro v
  rw [matrixHilbertOperator_conj, euclideanConj_norm]
  simpa only [euclideanConj_norm] using
    (matrixHilbertOperator A).le_opNorm (euclideanConj v)

private lemma matrixHilbertOperator_conj_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) :
    ‖matrixHilbertOperator (A.map star)‖ = ‖matrixHilbertOperator A‖ := by
  apply le_antisymm (matrixHilbertOperator_conj_norm_le A)
  have he : (A.map star).map star = A := by ext i j; simp
  have h := matrixHilbertOperator_conj_norm_le (A.map star)
  rwa [he] at h

private lemma matrixHilbertOperator_transpose_norm {ι κ : Type*}
    [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    ‖matrixHilbertOperator A.transpose‖ = ‖matrixHilbertOperator A‖ := by
  have hc : A.transpose = (A.conjTranspose).map star := by
    ext i j
    simp
  rw [hc, matrixHilbertOperator_conj_norm]
  change ‖LinearMap.toContinuousLinearMap A.conjTranspose.toEuclideanLin‖ = _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem finiteCubicBound_symm (S H : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (hH : ∀ h ∈ H, primary h) :
    finiteCubicBound S H = finiteCubicBound H S := by
  let A : Matrix H S ℂ := fun h a => cubicSymbol a.val h.val
  have hmat : (fun (a : S) (h : H) => cubicSymbol h.val a.val) = A.transpose := by
    funext a h
    exact cubic_reciprocity (hH h.val h.property) (hS a.val a.property)
  unfold finiteCubicBound finiteCubicOperator
  rw [hmat]
  exact congrArg (fun x : ℝ => x^2) (matrixHilbertOperator_transpose_norm A).symm

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
-- module Solutions.OAIQ096_CM.CubicGram_MellinDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma gramLogKernel_eq_radial (W : ℝ → ℂ) {ρ u : ℝ} (hρ : 0 ≤ ρ)
    (hu : |u| ≤ 1) :
    gramLogKernel W ρ u = radialDualProfile W (ρ * Real.exp u) := by
  have hcut : gramLogBump u = 1 := gramLogBump.one_of_mem_closedBall
    (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, gramLogBump] using hu)
  rw [gramLogKernel, hcut, one_smul, normProfileFourier_radial]
  congr 1
  rw [Complex.normSq_ofReal]
  calc
    (Real.sqrt ρ * Real.exp (u/2)) * (Real.sqrt ρ * Real.exp (u/2)) =
        (Real.sqrt ρ * Real.sqrt ρ) * (Real.exp (u/2) * Real.exp (u/2)) := by ring
    _ = ρ * Real.exp u := by
      rw [Real.mul_self_sqrt hρ, ← Real.exp_add]
      congr 2
      ring

lemma gramLogKernel_dyad_ratio (W : ℝ → ℂ) {ρ x y : ℝ} (hρ : 0 ≤ ρ)
    (hx : x ∈ Set.Icc (1 : ℝ) 2) (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    gramLogKernel W ρ (Real.log x - Real.log y) = radialDualProfile W (ρ*x/y) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hy0 : 0 < y := zero_lt_one.trans_le hy.1
  have hxlog : Real.log x ≤ 1 := (Real.log_le_sub_one_of_pos hx0).trans (by linarith [hx.2])
  have hylog : Real.log y ≤ 1 := (Real.log_le_sub_one_of_pos hy0).trans (by linarith [hy.2])
  have hlog : |Real.log x - Real.log y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Real.log_nonneg hx.1, Real.log_nonneg hy.1]
  rw [gramLogKernel_eq_radial W hρ hlog, Real.exp_sub,
    Real.exp_log hx0, Real.exp_log hy0, mul_div_assoc]

lemma gramMellinCoefficient_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (gramMellinCoefficient W hW hW' ρ) :=
  (𝓕 (gramLogSchwartz W hW hW' ρ)).integrable

theorem radialDualProfile_mellin_separated (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ} (hρ : 0 ≤ ρ)
    (hx : x ∈ Set.Icc (1 : ℝ) 2) (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    radialDualProfile W (ρ*x/y) = ∫ t : ℝ,
      gramMellinCoefficient W hW hW' ρ t * gramMellinPhase t x *
        star (gramMellinPhase t y) := by
  rw [← gramLogKernel_dyad_ratio W hρ hx hy]
  have he := congrArg (fun f : 𝓢(ℝ, ℂ) => f (Real.log x - Real.log y))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) (gramLogSchwartz W hW hW' ρ))
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at he
  rw [← gramLogSchwartz_apply W hW hW' ρ, ← he]
  apply integral_congr_ae
  filter_upwards with t
  have hi : inner ℝ t (Real.log x - Real.log y) =
      t * Real.log x - t * Real.log y := by
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hp : (Real.fourierChar (inner ℝ t (Real.log x - Real.log y)) : ℂ) =
      gramMellinPhase t x * star (gramMellinPhase t y) := by
    rw [hi, AddChar.map_sub_eq_div, div_eq_mul_inv, Circle.coe_mul,
      Circle.coe_inv_eq_conj]
    rfl
  change (Real.fourierChar (inner ℝ t (Real.log x - Real.log y)) : ℂ) *
      gramMellinCoefficient W hW hW' ρ t = _
  rw [hp]
  ring

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramExp_deriv_bound (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (i : ℕ), i ≤ n → ∀ u : ℝ, |u| ≤ 2 →
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ u ∈ Set.Icc (-2 : ℝ) 2,
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
  exact (hB i u (abs_le.mp hu)).trans
    ((le_abs_self (B i)).trans (hbi.trans (by dsimp [D]; linarith)))

lemma gramExp_scale_growth {c u : ℝ} (hc : 0 ≤ c) (hu : |u| ≤ 2) :
    1+c ≤ Real.exp 1 * (1+‖c • gramExp u‖) := by
  have hE : 1 ≤ Real.exp 1 := by simp
  have hEu : 1 ≤ Real.exp 1 * Real.exp (u/2) := by
    rw [← Real.exp_add]
    simpa using Real.exp_le_exp.mpr (show (0:ℝ) ≤ 1 + u/2 by
      linarith [(abs_le.mp hu).1])
  have hEc := mul_le_mul_of_nonneg_left hEu hc
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, gramExp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith

theorem schwartz_gramExp_comp_uniform (F : 𝓢(ℂ, ℂ)) (n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c → ∀ u : ℝ, |u| ≤ 2 →
      (1+c)^K * ‖iteratedFDeriv ℝ n (fun v => F (c • gramExp v)) u‖ ≤ C := by
  obtain ⟨D, hD, hderiv⟩ := gramExp_deriv_bound n
  let L := n+K
  let S := (Finset.Iic (L,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  let H := (Real.exp 1)^L * 2^L * S
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
      _ ≤ (Real.exp 1 * (1+‖c • gramExp u‖))^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ := by
        gcongr
        exact gramExp_scale_growth hc hu
      _ = (Real.exp 1)^L * ((1+‖c • gramExp u‖)^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖) := by rw [mul_pow]; ring
      _ ≤ (Real.exp 1)^L * (2^L*S) := mul_le_mul_of_nonneg_left hb (by positivity)
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

lemma annularLogSchwartz_deriv_zero (F : 𝓢(ℂ, ℂ)) (c u : ℝ) (n : ℕ)
    (hu : ¬ |u| ≤ 2) : iteratedFDeriv ℝ n (annularLogSchwartz F c) u = 0 := by
  by_contra hn
  have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := annularLogSchwartz F c) n hn
  have hb := tsupport_smul_subset_left (gramLogBump : ℝ → ℝ)
    (fun v => F (c • gramExp v)) hs
  rw [gramLogBump.tsupport_eq] at hb
  exact hu (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, gramLogBump] using hb)

theorem annularLogSchwartz_seminorm_uniform (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (annularLogSchwartz F c) ≤ C := by
  choose C hC hbound using fun i => schwartz_gramExp_comp_uniform F i K
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i gramBumpSchwartz * C (n-i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hC (n-i)))
  refine ⟨2^k * B, by positivity, ?_⟩
  intro c hc
  have hp : 0 < (1+c)^K := pow_pos (by positivity) _
  rw [← le_div_iff₀' hp]
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ 2
  · rw [le_div_iff₀' hp]
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) gramLogBump.contDiff
      ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)) u (n := n) (mod_cast le_top)
    have hd' : (1+c)^K * ‖iteratedFDeriv ℝ n (annularLogSchwartz F c) u‖ ≤ B := by
      calc
        _ ≤ (1+c)^K * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i gramLogBump u‖ *
              ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖ :=
          mul_le_mul_of_nonneg_left hd hp.le
        _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i gramLogBump u‖ *
              ((1+c)^K * ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ B := by
          apply Finset.sum_le_sum
          intro i hi
          have hb : ‖iteratedFDeriv ℝ i gramLogBump u‖ ≤
              SchwartzMap.seminorm ℝ 0 i gramBumpSchwartz := by
            have hb := SchwartzMap.le_seminorm ℝ 0 i gramBumpSchwartz u
            rw [show (gramBumpSchwartz : ℝ → ℝ) = (gramLogBump : ℝ → ℝ) from rfl] at hb
            simpa only [pow_zero, one_mul] using hb
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity))
            (hbound (n-i) c hc u hu) (by positivity) (by positivity)
    calc
      _ = ‖u‖^k * ((1+c)^K * ‖iteratedFDeriv ℝ n (annularLogSchwartz F c) u‖) := by ring
      _ ≤ 2^k * B := mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hu) k) hd' (by positivity) (by positivity)
  · rw [annularLogSchwartz_deriv_zero F c u n hu, norm_zero, mul_zero]
    positivity

theorem annularLogSchwartz_fourier_uniform (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (𝓕 (annularLogSchwartz F c)) ≤ C := by
  let f : ℝ → 𝓢(ℝ, ℂ) := fun c => (1+c)^K • annularLogSchwartz F c
  have hb : Bornology.IsVonNBounded ℝ (f '' Set.Ici 0) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C, hC, hc⟩ := annularLogSchwartz_seminorm_uniform F i.1 i.2 K
    refine ⟨C+1, by linarith, ?_⟩
    intro c hc0
    have hc0' : 0 ≤ c := hc0
    change SchwartzMap.seminorm ℝ i.1 i.2 ((1+c)^K • annularLogSchwartz F c) < _
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
    (SchwartzMap.fourierTransformCLM ℝ ((1+c)^K • annularLogSchwartz F c)) < C at h
  rw [map_smul, map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos (pow_pos (by linarith) _)] at h
  exact h.le

theorem annularLogSchwartz_fourier_L1_uniform (F : 𝓢(ℂ, ℂ)) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * (∫ t : ℝ, ‖𝓕 (annularLogSchwartz F c) t‖) ≤ C := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k * ∫ t : ℝ, (1+‖t‖)^(-(k : ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun t => by positivity))
  obtain ⟨C₀, hC₀, hc₀⟩ := annularLogSchwartz_fourier_uniform F 0 0 K
  obtain ⟨C₁, hC₁, hc₁⟩ := annularLogSchwartz_fourier_uniform F k 0 K
  refine ⟨D*(C₀+C₁)+1, by positivity, ?_⟩
  intro c hc
  have h := (𝓕 (annularLogSchwartz F c)).integral_pow_mul_iteratedFDeriv_le ℝ volume 0 0
  simp only [pow_zero, norm_iteratedFDeriv_zero, one_mul, zero_add] at h
  have hb : (1+c)^K * (∫ t : ℝ, ‖𝓕 (annularLogSchwartz F c) t‖) ≤ D*(C₀+C₁) := by
    calc
      _ ≤ (1+c)^K * (D * (SchwartzMap.seminorm ℝ 0 0 (𝓕 (annularLogSchwartz F c)) +
            SchwartzMap.seminorm ℝ k 0 (𝓕 (annularLogSchwartz F c)))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = D*((1+c)^K * SchwartzMap.seminorm ℝ 0 0 (𝓕 (annularLogSchwartz F c)) +
            (1+c)^K * SchwartzMap.seminorm ℝ k 0 (𝓕 (annularLogSchwartz F c))) := by ring
      _ ≤ D*(C₀+C₁) := mul_le_mul_of_nonneg_left (add_le_add (hc₀ c hc) (hc₁ c hc)) hD
  linarith

lemma annularLogSchwartz_eq_gramLogSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    annularLogSchwartz (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ) =
      gramLogSchwartz W hW hW' ρ := by
  ext u
  simp only [annularLogSchwartz_apply, gramLogSchwartz_apply, gramLogKernel,
    normProfileFourierSchwartz_apply]
  congr 2
  simp only [gramExp, Complex.real_smul, Complex.ofReal_mul]

theorem gramMellinCoefficient_mass_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * (∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖) ≤ C := by
  obtain ⟨C, hC, hc⟩ := annularLogSchwartz_fourier_L1_uniform
    (normProfileFourierSchwartz W hW hW') (2*A)
  refine ⟨C, hC, ?_⟩
  intro ρ hρ
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ, Real.sqrt_nonneg ρ]
  have h := hc (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [annularLogSchwartz_eq_gramLogSchwartz W hW hW' ρ] at h
  exact (mul_le_mul_of_nonneg_right hs (integral_nonneg (fun t => _root_.norm_nonneg _))).trans h

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma gramMellinCoefficient_integrable_phases (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ x y : ℝ) :
    Integrable (fun t => gramMellinCoefficient W hW hW' ρ t * gramMellinPhase t x *
      star (gramMellinPhase t y)) := by
  apply Integrable.mul_bdd (c := 1)
  · exact (gramMellinCoefficient_integrable W hW hW' ρ).mul_bdd
      (gramMellinPhase_continuous x).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_gramMellinPhase t x).le))
  · exact (gramMellinPhase_continuous y).star.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp)

lemma thinDyad_mul {x y : ℝ} (hx : x ∈ Icc (1 : ℝ) (Real.sqrt 2))
    (hy : y ∈ Icc (1 : ℝ) (Real.sqrt 2)) : x*y ∈ Icc (1 : ℝ) 2 := by
  constructor
  · calc
      1 = 1*1 := by norm_num
      _ ≤ x*y := mul_le_mul hx.1 hy.1 (by norm_num) (by linarith [hx.1])
  · calc
      _ ≤ Real.sqrt 2 * Real.sqrt 2 :=
        mul_le_mul hx.2 hy.2 (by linarith [hy.1]) (Real.sqrt_nonneg _)
      _ = 2 := Real.mul_self_sqrt (by norm_num)

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

theorem coprimeRadialForm_mellin (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, x h ∈ Icc (1 : ℝ) 2)
    (hy : ∀ a ∈ S, y a ∈ Icc (1 : ℝ) (Real.sqrt 2))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    coprimeRadialForm S H v w phase x y W ρ = ∫ t : ℝ,
      gramMellinCoefficient W hW hW' ρ t * coprimeMellinKernel S H v w phase x y t := by
  let F (h a b : Eisenstein) (t : ℝ) : ℂ :=
    (phase h * (if IsCoprime a b then
      (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0)) *
      (gramMellinCoefficient W hW hW' ρ t * gramMellinPhase t (x h) *
        star (gramMellinPhase t (y a*y b)))
  have hF (h a b : Eisenstein) : Integrable (F h a b) :=
    (gramMellinCoefficient_integrable_phases W hW hW' ρ (x h) (y a*y b)).const_mul _
  have he (h : Eisenstein) (hh : h ∈ H) (a : Eisenstein) (ha : a ∈ S)
      (b : Eisenstein) (hb : b ∈ S) :
      phase h * (if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) *
          radialDualProfile W (ρ*x h/(y a*y b)) else 0) = ∫ t, F h a b t := by
    rw [show (∫ t, F h a b t) = _ from integral_const_mul _ _]
    rw [← radialDualProfile_mellin_separated W hW hW' hρ (hx h hh)
      (thinDyad_mul (hy a ha) (hy b hb))]
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
      rw [gramMellinPhase_mul t (zero_lt_one.trans_le (hy a ha).1)
        (zero_lt_one.trans_le (hy b hb).1), star_mul]
      split_ifs <;> simp only [star_mul, mul_zero] <;> ring

end CubicFirstMoment

namespace CubicFirstMoment

theorem coprimeRadialForm_norm_le (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, x h ∈ Icc (1 : ℝ) 2)
    (hy : ∀ a ∈ S, y a ∈ Icc (1 : ℝ) (Real.sqrt 2))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
      (∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖) *
        coprimeNormMajorant S H U v w := by
  have hc := gramMellinCoefficient_integrable W hW hW' ρ
  have hi := hc.mul_bdd
    (coprimeMellinKernel_continuous S H v w phase x y).aestronglyMeasurable
    (Eventually.of_forall
      (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y))
  rw [coprimeRadialForm_mellin S H v w phase x y hx hy W hW hW' hρ]
  calc
    _ ≤ ∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t *
        coprimeMellinKernel S H v w phase x y t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖ *
        coprimeNormMajorant S H U v w := by
      apply integral_mono hi.norm (hc.norm.mul_const _)
      intro t
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y t)
        (_root_.norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem coprimeRadialForm_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H U : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      (∀ p ∈ U, primaryPrime p) →
      (∀ a ∈ S, primaryPrimeFactors a ⊆ U) →
      ∀ (v w phase : Eisenstein → ℂ), (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      ∀ (x y : Eisenstein → ℝ),
      (∀ h ∈ H, x h ∈ Icc (1 : ℝ) 2) →
      (∀ a ∈ S, y a ∈ Icc (1 : ℝ) (Real.sqrt 2)) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
        C * coprimeNormMajorant S H U v w := by
  obtain ⟨C, hC, hc⟩ := gramMellinCoefficient_mass_rapidDecay W hW hW' A
  refine ⟨C, hC, ?_⟩
  intro S H U hS hU hSU v w phase hphase x y hx hy ρ hρ
  calc
    _ ≤ (1+ρ)^A * ((∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖) *
        coprimeNormMajorant S H U v w) :=
      mul_le_mul_of_nonneg_left
        (coprimeRadialForm_norm_le S H U hS hU hSU v w phase hphase x y hx hy W hW hW' hρ)
        (by positivity)
    _ = ((1+ρ)^A * (∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖)) *
        coprimeNormMajorant S H U v w := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hc ρ hρ) (coprimeNormMajorant_nonneg _ _ _ _ _)

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

theorem coprimePoissonDyad_norm_recurrence (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (u : Eisenstein → ℂ) (Z J N : ℝ), 0 ≤ Z → 0 < J → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) →
      (1+Z*J/(27*N^2))^A * ‖coprimePoissonDyad S H u W Z‖ ≤
        C*(Z/N)*finiteCubicBound S H *
          ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprimeRadialForm_rapidDecay W hW hW' A
  refine ⟨C/9, by positivity, ?_⟩
  intro S H hS u Z J N hZ hJ hN hSN hHJ
  let U := sievePrimeSet S
  have hU : ∀ p ∈ U, primaryPrime p := sievePrimeSet_primary S (fun a ha => (hS a ha).1)
  have hu : ∀ a ∈ S, primaryPrimeFactors a ⊆ U := fun a ha => factors_subset_sievePrimeSet ha
  have hx : ∀ h ∈ H, norm h/J ∈ Icc (1 : ℝ) 2 := by
    intro h hh
    exact ⟨(le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1),
      (div_le_iff₀ hJ).mpr (hHJ h hh).2⟩
  have hy : ∀ a ∈ S, norm a/N ∈ Icc (1 : ℝ) (Real.sqrt 2) := by
    intro a ha
    exact ⟨(le_div_iff₀ hN).mpr (by simpa using (hSN a ha).1),
      (div_le_iff₀ hN).mpr (hSN a ha).2⟩
  have hi := hbound S H U hS hU hu (gaussRowCoefficient u) (gaussRowCoefficient u)
    (fun h => (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ))
    (fun h hh => by simp only [Circle.norm_coe, le_refl])
    (fun h => norm h/J) (fun a => norm a/N) hx hy (Z*J/(27*N^2)) (by positivity)
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
        (gaussRowCoefficient_divisor_energy S hS u hN (fun a ha => (hSN a ha).1))
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

lemma finiteCubicBound_le_card_mul (S H : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) :
    finiteCubicBound S H ≤ (S.card : ℝ)*H.card := by
  apply (finiteCubicBound_le_iff S H (by positivity)).mpr
  intro u
  have hrow (h : Eisenstein) :
      ‖∑ a ∈ S, u a*cubicSymbol a h‖^2 ≤ (S.card : ℝ)*∑ a ∈ S, ‖u a‖^2 := by
    have ht : ‖∑ a ∈ S, u a*cubicSymbol a h‖ ≤ ∑ a ∈ S, ‖u a‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS a ha) h)
    have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun a => ‖u a‖)
    simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
    exact (pow_le_pow_left₀ (_root_.norm_nonneg _) ht 2).trans hc
  calc
    _ ≤ ∑ _h ∈ H, (S.card : ℝ)*∑ a ∈ S, ‖u a‖^2 := Finset.sum_le_sum (fun h _ => hrow h)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

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

lemma hasSum_coprimePoissonDyad (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ ¬ IsUnit a)
    (u : Eisenstein → ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) :
    HasSum (fun j : ℕ => coprimePoissonDyad S (frequencyDyad j) u W Z)
      (coprimeGramForm S u W Z) := by
  unfold coprimePoissonDyad coprimeGramForm
  apply hasSum_sum
  intro a ha
  apply hasSum_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    have hne : a ≠ b := by
      intro he
      exact (hS a ha).2.2 (isCoprime_self.mp (he ▸ hab))
    have hf := (hasSum_frequencyDyad (gramDualTerm a b W Z)
      (summable_gramDualTerm (hS a ha).1 (hS b hb).1 W hW hW' hZ)
      (gramDualTerm_zero (hS a ha).1 (hS b hb).1 (hS a ha).2.1 (hS b hb).2.1 hab hne W Z)).mul_left
      (u a*star (u b)*((Z/(9*Real.sqrt (norm (a*b))) : ℝ) : ℂ)*(gauss a*star (gauss b)))
    convert hf using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    rw [primaryCharacterGram_poisson_normalized (hS a ha).1 (hS b hb).1
      (hS a ha).2.1 (hS b hb).2.1 hab W hW hW' hZ]
    ring
  · simp only [ite_eq_right hab]
    exact hasSum_zero

lemma frequencyDyad_card_le (j : ℕ) :
    ((frequencyDyad j).card : ℝ) ≤ 36*(2 : ℝ)^j := by
  have hs : frequencyDyad j ⊆ nonzeroNormBall ((2 : ℝ)^(j+1)) := Finset.filter_subset _ _
  have hh : ((frequencyDyad j).card : ℝ) ≤ (nonzeroNormBall ((2 : ℝ)^(j+1))).card := by
    exact_mod_cast Finset.card_le_card hs
  exact hh.trans ((nonzeroNormBall_card_le (by positivity)).trans_eq (by rw [pow_succ]; ring))

theorem coprimeGramForm_base_bound (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ ¬ IsUnit a) →
      ∀ (u : Eisenstein → ℂ) (Z N : ℝ), 0 < Z → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ‖coprimeGramForm S u W Z‖ ≤ C*N*S.card*
        ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprimePoissonDyad_norm_recurrence W hW hW' 2
  refine ⟨1944*C,by positivity,?_⟩
  intro S hS u Z N hZ hN hSN
  let E : ℝ := ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun a _ => by positivity)
  let c : ℝ := Z/(27*N^2)
  have hc : 0 < c := by dsimp [c]; positivity
  let D : ℝ := 36*C*(Z/N)*S.card*E
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hterm (j : ℕ) : ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ ≤
      D*((2 : ℝ)^j/(1+c*2^j)^2) := by
    have hj : 0 < (2 : ℝ)^j := by positivity
    have hd : 0 < (1+c*2^j)^2 := by positivity
    have hrec := hbound S (frequencyDyad j) (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
      u Z ((2 : ℝ)^j) N hZ.le hj hN hSN (fun h hh => frequencyDyad_norm hh)
    have he : Z*2^j/(27*N^2) = c*2^j := by dsimp [c]; ring
    rw [he] at hrec
    have hb : finiteCubicBound S (frequencyDyad j) ≤ 36*S.card*(2 : ℝ)^j := by
      exact (finiteCubicBound_le_card_mul S _ (fun a ha => (hS a ha).1)).trans
        ((mul_le_mul_of_nonneg_left (frequencyDyad_card_le j) (by positivity)).trans_eq (by ring))
    calc
      _ ≤ C*(Z/N)*finiteCubicBound S (frequencyDyad j)*E/(1+c*2^j)^2 := by
        apply (le_div_iff₀ hd).mpr
        simpa only [mul_comm, E] using hrec
      _ ≤ C*(Z/N)*(36*S.card*2^j)*E/(1+c*2^j)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (by positivity)) hE) hd.le
      _ = _ := by dsimp [D]; ring
  have hmajor := (dyadic_decay_summable hc).mul_left D
  have hsum := hasSum_coprimePoissonDyad S hS u W hW hW' hZ
  calc
    _ = ‖∑' j : ℕ, coprimePoissonDyad S (frequencyDyad j) u W Z‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' j : ℕ, ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ := norm_tsum_le_tsum_norm hsum.summable.norm
    _ ≤ ∑' j : ℕ, D*((2 : ℝ)^j/(1+c*2^j)^2) :=
      Summable.tsum_le_tsum (fun j => hterm j) hsum.summable.norm hmajor
    _ = D*(∑' j : ℕ, (2 : ℝ)^j/(1+c*2^j)^2) := tsum_mul_left
    _ ≤ D*(2/c) := mul_le_mul_of_nonneg_left (dyadic_decay_tsum hc) hD
    _ = _ := by
      dsimp [D,c,E]
      field_simp
      ring

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

theorem primarySmoothedSieveMass_common_blocks (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    primarySmoothedSieveMass S u W Z =
      ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        let m := ∏ p ∈ s, p
        (idealMoebius m : ℂ) *
          coprimeGramForm (residualRows S k) (commonBlockCoefficient u k m) W (Z/norm m) := by
  rw [primarySmoothedSieveMass_gram S (fun a ha => (hS a ha).1) u W hW hW' hZ,
    common_factor_matrix_decomposition S hS]
  apply Finset.sum_congr rfl
  intro k hkS
  have hk := commonRowFactors_spec hS hkS
  have hr := residualRows_primary hk.1 hS
  calc
    _ = ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        ∑ s ∈ (primaryPrimeFactors k).powerset,
          let m := ∏ p ∈ s, p
          (idealMoebius m : ℂ) *
            (if IsCoprime a b then commonBlockCoefficient u k m a *
              star (commonBlockCoefficient u k m b) * primaryCharacterGram a b W (Z/norm m) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab : IsCoprime a b
      · simp only [ite_eq_left hab]
        rw [primaryCharacterGram_common_factor hk.1 hk.2 (hr a ha).1 (hr b hb).1 W hW hW' hZ]
        rw [Finset.mul_sum]
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
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma finiteCubicBound_biUnion {ι : Type*} (I : Finset ι) (P : Finset Eisenstein)
    (H : ι → Finset Eisenstein) :
    finiteCubicBound P (I.biUnion H) ≤ ∑ i ∈ I, finiteCubicBound P (H i) := by
  apply (finiteCubicBound_le_iff _ _ (Finset.sum_nonneg (fun _ _ => finiteCubicBound_nonneg _ _))).mpr
  intro u
  have hmass : (∑ n ∈ I.biUnion H, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
      ∑ i ∈ I, ∑ n ∈ H i, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      rw [Finset.biUnion_insert,Finset.sum_insert hi]
      have he := Finset.sum_union_inter (s₁ := H i) (s₂ := I.biUnion H)
        (f := fun n => ‖∑ b ∈ P, u b*cubicSymbol b n‖^2)
      have hn : 0 ≤ ∑ n ∈ H i ∩ I.biUnion H, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      linarith
  calc
    _ ≤ ∑ i ∈ I, ∑ n ∈ H i, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := hmass
    _ ≤ ∑ i ∈ I, finiteCubicBound P (H i)*∑ b ∈ P, ‖u b‖^2 :=
      Finset.sum_le_sum (fun i _ => finiteCubicBound_controls_mass _ _ _)
    _ = _ := by rw [Finset.sum_mul]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GlobalRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma residualRows_norm {S : Finset Eisenstein} {k : Eisenstein} (hk : primary k)
    {N : ℝ} (hS : ∀ p ∈ S, N ≤ norm p ∧ norm p ≤ Real.sqrt 2*N) :
    ∀ a ∈ residualRows S k, N/norm k ≤ norm a ∧ norm a ≤ Real.sqrt 2*(N/norm k) := by
  have hn : 0 < norm k := norm_pos_of_ne_zero (primary_ne_zero hk)
  intro a ha
  have hh := hS (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
  rw [show norm (k*a) = norm k*norm a from Complex.normSq_mul _ _] at hh
  constructor
  · exact (div_le_iff₀ hn).mpr (by nlinarith [hh.1])
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hn).mpr
    nlinarith [hh.2]

lemma residualRows_nonunit {S : Finset Eisenstein} {k : Eisenstein} (hk : primary k)
    {N : ℝ} (hNk : norm k < N) (hS : ∀ p ∈ S, N ≤ norm p) :
    ∀ a ∈ residualRows S k, ¬ IsUnit a := by
  intro a ha hu
  have hh := hS (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
  rw [show norm (k*a) = norm k*norm a from Complex.normSq_mul _ _,norm_of_isUnit hu,mul_one] at hh
  exact (not_lt_of_ge hh) hNk

lemma residualRows_subset_one {S : Finset Eisenstein} {k : Eisenstein} (hk : primary k)
    (hS : ∀ p ∈ S, primary p) {N : ℝ} (hNk : N ≤ norm k)
    (hSN : ∀ p ∈ S, norm p ≤ Real.sqrt 2*N) :
    residualRows S k ⊆ {1} := by
  intro a ha
  have hp := hS (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
  have hpa := primary_of_mul hk hp
  have hpos : 0 < norm k := norm_pos_of_ne_zero (primary_ne_zero hk)
  have hna : norm a ≤ Real.sqrt 2 := by
    have hh := hSN (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
    rw [show norm (k*a) = norm k*norm a from Complex.normSq_mul _ _] at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hNk (Real.sqrt_nonneg _))
    nlinarith
  have hna' : norm a < 2 := hna.trans_lt (by norm_num : Real.sqrt (2 : ℝ) < 2)
  have hone : norm a = 1 := by
    have hltreal : (normNat a : ℝ) < (2 : ℝ) := by rw [normNat_cast]; exact hna'
    have hlt : normNat a < 2 := by exact_mod_cast hltreal
    have hnz := normNat_ne_zero_of_ne_zero (primary_ne_zero hpa)
    rw [← normNat_cast,show normNat a = 1 by omega,Nat.cast_one]
  exact Finset.mem_singleton.mpr (primary_unit_eq_one (isUnit_of_norm_eq_one hone) hpa)

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimeGramForm_subset_singleton (R : Finset Eisenstein) (hR : R ⊆ {1})
    (v : Eisenstein → ℂ) (W : ℝ → ℂ) (Z : ℝ) :
    ‖coprimeGramForm R v W Z‖ ≤
      ‖primaryCharacterGram 1 1 W Z‖ * ∑ a ∈ R, ‖v a‖^2 := by
  by_cases h1 : (1 : Eisenstein) ∈ R
  · have he : R = {1} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨h1,fun a ha => Finset.mem_singleton.mp (hR ha)⟩
    simp only [coprimeGramForm,he,Finset.sum_singleton,isCoprime_one_left,ite_true, if_true,
      norm_mul,norm_star]
    exact le_of_eq (by ring)
  · have he : R = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun a ha =>
      h1 ((Finset.mem_singleton.mp (hR ha)) ▸ ha))
    simp [coprimeGramForm,he]

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

lemma primaryCharacterGram_one_one_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : Continuous W) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 0 < Z → ‖primaryCharacterGram 1 1 W Z‖ ≤ C*Z := by
  obtain ⟨R,hR,hR0⟩ := hW.exists_pos_le_norm
  obtain ⟨L,hL⟩ := hW'.bounded_above_of_compact_support hW
  let K := max L 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hLK : L ≤ K := le_max_left _ _
  refine ⟨18*R*K,by positivity,?_⟩
  intro Z hZ
  have hs : primaryCharacterGram 1 1 W Z =
      ∑ n ∈ nonzeroNormBall (R*Z), if primary n then
        W (norm n/Z)*cubicSymbol 1 n*star (cubicSymbol 1 n) else 0 := by
    apply tsum_eq_sum
    intro n hn
    split_ifs with hp
    · have hn' : R*Z < norm n := lt_of_not_ge (fun h =>
        hn (mem_nonzeroNormBall.mpr ⟨h,primary_ne_zero hp⟩))
      have hw : W (norm n/Z) = 0 := hR0 _ (by
        rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) (le_of_lt hZ))]
        exact (le_div_iff₀ hZ).mpr hn'.le)
      simp [hw]
    · rfl
  rw [hs]
  calc
    _ ≤ ∑ n ∈ nonzeroNormBall (R*Z),
        ‖if primary n then W (norm n/Z)*cubicSymbol 1 n*star (cubicSymbol 1 n) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ nonzeroNormBall (R*Z), K := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs with hp
      · rw [norm_mul,norm_mul,norm_star]
        calc
          _ ≤ ‖W (norm n/Z)‖*1*1 := by
            gcongr <;> exact norm_cubicSymbol_le_one primary_one n
          _ ≤ K := by simpa using (hL (norm n/Z)).trans hLK
      · simpa using hK.le
    _ = (nonzeroNormBall (R*Z)).card*K := by simp
    _ ≤ (18*(R*Z))*K := mul_le_mul_of_nonneg_right (nonzeroNormBall_card_le (by positivity)) hK.le
    _ = _ := by ring

lemma cubicSieveCutoff_compact : HasCompactSupport cubicSieveCutoff :=
  gramLogBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

lemma cubicSieveCutoff_smooth : ContDiff ℝ ∞ cubicSieveCutoff :=
  Complex.ofRealCLM.contDiff.comp gramLogBump.contDiff

lemma cubicSieveCutoff_zero {t : ℝ} (ht : 2 ≤ |t|) : cubicSieveCutoff t = 0 := by
  have h := gramLogBump.zero_of_le_dist (x := t)
  have he : gramLogBump t = 0 := h (by
    simpa only [Real.dist_eq,sub_zero,gramLogBump] using ht)
  simp [cubicSieveCutoff,he]

lemma cubicSieveCutoff_one {t : ℝ} (ht : |t| ≤ 1) : cubicSieveCutoff t = 1 := by
  have he : gramLogBump t = 1 := gramLogBump.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,gramLogBump] using ht)
  simp [cubicSieveCutoff,he]

lemma primarySmoothedSieveMass_cutoff (S : Finset Eisenstein) (u : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 < M) :
    primarySmoothedSieveMass S u cubicSieveCutoff M =
      ∑ x ∈ nonzeroNormBall (2*M), if primary x then
        cubicSieveCutoff (norm x/M)*(‖∑ n ∈ S, u n*cubicSymbol n x‖^2 : ℝ) else 0 := by
  apply tsum_eq_sum
  intro x hx
  split_ifs with hp
  · have hn : 2*M < norm x := lt_of_not_ge (fun h =>
      hx (mem_nonzeroNormBall.mpr ⟨h,primary_ne_zero hp⟩))
    have hw : cubicSieveCutoff (norm x/M) = 0 := cubicSieveCutoff_zero (by
      rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hM.le)]
      exact (le_div_iff₀ hM).mpr hn.le)
    simp [hw]
  · rfl

lemma finiteCubicMass_le_smoothed (S H : Finset Eisenstein)
    (hH : ∀ x ∈ H, primary x) (u : Eisenstein → ℂ) {M : ℝ} (hM : 0 < M)
    (hHM : ∀ x ∈ H, norm x ≤ M) :
    (∑ x ∈ H, ‖∑ n ∈ S, u n*cubicSymbol n x‖^2) ≤
      ‖primarySmoothedSieveMass S u cubicSieveCutoff M‖ := by
  have hsub : H ⊆ nonzeroNormBall (2*M) := by
    intro x hx
    exact mem_nonzeroNormBall.mpr ⟨(hHM x hx).trans (by linarith),primary_ne_zero (hH x hx)⟩
  have hreal := (Complex.re_le_norm (primarySmoothedSieveMass S u cubicSieveCutoff M))
  apply le_trans _ hreal
  rw [primarySmoothedSieveMass_cutoff S u hM,Complex.re_sum]
  have he (x : Eisenstein) (hx : x ∈ H) :
      (if primary x then cubicSieveCutoff (norm x/M)*
        (‖∑ n ∈ S, u n*cubicSymbol n x‖^2 : ℝ) else 0).re =
        ‖∑ n ∈ S, u n*cubicSymbol n x‖^2 := by
    rw [ite_eq_left (hH x hx),cubicSieveCutoff_one]
    · norm_cast; simp
    · rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hM.le)]
      exact (div_le_one hM).mpr (hHM x hx)
  rw [← Finset.sum_congr rfl he]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro x hx hxH
  split_ifs
  · simp only [cubicSieveCutoff,← Complex.ofReal_mul,Complex.ofReal_re]
    exact mul_nonneg gramLogBump.nonneg (sq_nonneg _)
  · simp

end CubicFirstMoment
end
end

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
-- module Solutions.OAIQ096_CM.CubicGram_SieveBase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Base bounds for thin smoothed cubic sieve families. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma thin_primary_card_le {S : Finset Eisenstein} {N : ℝ} (hN : 0 < N)
    (hS : ∀ a ∈ S, primary a) (hSN : ∀ a ∈ S, norm a ≤ Real.sqrt 2*N) :
    (S.card : ℝ) ≤ 36*N := by
  have hs : S ⊆ nonzeroNormBall (2*N) := by
    intro a ha
    have h2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sqrt_nonneg 2]
    exact mem_nonzeroNormBall.mpr ⟨(hSN a ha).trans (mul_le_mul_of_nonneg_right h2 hN.le),primary_ne_zero (hS a ha)⟩
  calc
    _ ≤ ((nonzeroNormBall (2*N)).card : ℝ) := by exact_mod_cast Finset.card_le_card hs
    _ ≤ 18*(2*N) := nonzeroNormBall_card_le (by positivity)
    _ = _ := by ring

theorem primarySmoothedSieveMass_base_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (u : Eisenstein → ℂ) (Z N : ℝ), 0 < Z → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ‖primarySmoothedSieveMass S u W Z‖ ≤ C*(Z+N^2)*
        ∑ k ∈ commonRowFactors S, (2 : ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S u k := by
  obtain ⟨C₀,hC₀,hrec⟩ := coprimeGramForm_base_bound W hW hW'
  obtain ⟨D,hD,hdiag⟩ := primaryCharacterGram_one_one_bound W hW hW'.continuous
  let C := max (36*C₀) D
  have hC : 0 < C := hD.trans_le (le_max_right _ _)
  have hC₀C : 36*C₀ ≤ C := le_max_left _ _
  have hDC : D ≤ C := le_max_right _ _
  refine ⟨C,hC,?_⟩
  intro S hS u Z N hZ hN hSN
  have hblock (k : Eisenstein) (hkS : k ∈ commonRowFactors S)
      (s : Finset Eisenstein) (hs : s ∈ (primaryPrimeFactors k).powerset) :
      let m := ∏ p ∈ s, p
      ‖(idealMoebius m : ℂ)*coprimeGramForm (residualRows S k)
        (commonBlockCoefficient u k m) W (Z/norm m)‖ ≤
        C*(Z+N^2)*commonBlockEnergy S u k := by
    dsimp only
    let m := ∏ p ∈ s, p
    have hk := commonRowFactors_spec hS hkS
    have hm : primary m := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).1.1)
    have hnk : 0 < norm k := norm_pos_of_ne_zero (primary_ne_zero hk.1)
    have hnm : 0 < norm m := norm_pos_of_ne_zero (primary_ne_zero hm)
    have hnk1 : 1 ≤ norm k := one_le_norm (primary_ne_zero hk.1)
    have hnm1 : 1 ≤ norm m := one_le_norm (primary_ne_zero hm)
    have hrpos : 0 < N/norm k := div_pos hN hnk
    have hrle : N/norm k ≤ N := (div_le_self hN.le hnk1)
    have hzle : Z/norm m ≤ Z := (div_le_self hZ.le hnm1)
    have hre := residualRows_primary hk.1 hS
    have hh : ‖coprimeGramForm (residualRows S k) (commonBlockCoefficient u k m) W (Z/norm m)‖ ≤
        C*(Z+N^2)*commonBlockEnergy S u k := by
      by_cases hkN : norm k < N
      · have hb := hrec (residualRows S k)
          (fun a ha => ⟨(hre a ha).1,(hre a ha).2,
            residualRows_nonunit hk.1 hkN (fun p hp => (hSN p hp).1) a ha⟩)
          (commonBlockCoefficient u k m) (Z/norm m) (N/norm k)
          (div_pos hZ hnm) hrpos (residualRows_norm hk.1 hSN)
        have hc := thin_primary_card_le hrpos (fun a ha => (hre a ha).1)
          (fun a ha => (residualRows_norm hk.1 hSN a ha).2)
        have hbC : C₀*(N/norm k)*(residualRows S k).card ≤ C*(Z+N^2) := by
          calc
            _ ≤ C₀*N*(36*N) := by gcongr; exact hc.trans (by gcongr)
            _ = (36*C₀)*N^2 := by ring
            _ ≤ C*N^2 := mul_le_mul_of_nonneg_right hC₀C (sq_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hC.le
        apply hb.trans
        exact mul_le_mul hbC (commonBlockCoefficient_energy_le S hS u hk.1 m)
          (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
      · calc
          _ ≤ ‖primaryCharacterGram 1 1 W (Z/norm m)‖ *
              ∑ a ∈ residualRows S k, ‖commonBlockCoefficient u k m a‖^2 :=
            coprimeGramForm_subset_singleton _
              (residualRows_subset_one hk.1 (fun p hp => (hS p hp).1) (le_of_not_gt hkN)
                (fun p hp => (hSN p hp).2)) _ _ _
          _ ≤ (D*(Z/norm m))*commonBlockEnergy S u k :=
            mul_le_mul (hdiag _ (div_pos hZ hnm))
              (commonBlockCoefficient_unweighted_energy_le S hS u hk.1 m)
              (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right (by
            calc
              D*(Z/norm m) ≤ D*Z := mul_le_mul_of_nonneg_left hzle hD.le
              _ ≤ C*Z := mul_le_mul_of_nonneg_right hDC hZ.le
              _ ≤ C*(Z+N^2) := mul_le_mul_of_nonneg_left (by nlinarith) hC.le)
            (commonBlockEnergy_nonneg S u k)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one m)).trans hh
  rw [primarySmoothedSieveMass_common_blocks S hS u W hW hW' hZ]
  calc
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        ‖(idealMoebius (∏ p ∈ s, p) : ℂ)*coprimeGramForm (residualRows S k)
          (commonBlockCoefficient u k (∏ p ∈ s, p)) W (Z/norm (∏ p ∈ s, p))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => norm_sum_le _ _))
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        C*(Z+N^2)*commonBlockEnergy S u k :=
      Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun s hs => hblock k hk s hs))
    _ = _ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k hk
                ring

theorem finiteCubicBound_base_thin (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ),
      0 < M → 0 < N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*N^ε*(M+N^2) := by
  obtain ⟨C₀,hC₀,hrec⟩ := primarySmoothedSieveMass_base_bound cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth
  obtain ⟨D,hD,henergy⟩ := common_energy_small_power ε hε
  refine ⟨C₀*D*(Real.sqrt 2)^ε,by positivity,?_⟩
  intro S H M N hM hN hS hH
  apply (finiteCubicBound_le_iff _ _ (by positivity)).mpr
  intro u
  calc
    _ ≤ ‖primarySmoothedSieveMass S u cubicSieveCutoff M‖ :=
      finiteCubicMass_le_smoothed S H (fun x hx => (hH x hx).1) u hM (fun x hx => (hH x hx).2)
    _ ≤ C₀*(M+N^2)*(D*(Real.sqrt 2*N)^ε *∑ a ∈ S, ‖u a‖^2) :=
      (hrec S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) u M N hM hN
        (fun a ha => (hS a ha).2.2)).trans (mul_le_mul_of_nonneg_left
          (henergy S u (Real.sqrt 2*N) (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩))
          (by positivity))
    _ = _ := by rw [Real.mul_rpow (Real.sqrt_nonneg 2) hN.le]; ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveExponent
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative cube and dual bounds under a sieve exponent. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma dyadic_polynomial_small_power (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ((j : ℝ)+2)^d ≤ C*((2 : ℝ)^j)^ε := by
  let r : ℝ := (2^ε)⁻¹
  have hp : (1 : ℝ) < 2^ε := Real.one_lt_rpow (by norm_num) hε
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ hp
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d (r := r) (by simpa only [Real.norm_eq_abs,abs_of_pos hr] using hr1)
  let D : ℝ := (∑' n : ℕ, (n : ℝ)^d*r^n)+1
  have hD : 0 < D := by
    have hh : 0 ≤ ∑' n : ℕ, (n : ℝ)^d*r^n := tsum_nonneg (fun n => by positivity)
    dsimp [D]; linarith
  refine ⟨D*(2^ε)^2,by positivity,?_⟩
  intro j
  have hh := hs.le_tsum (j+2) (fun n _ => by positivity)
  have hh' : (((j : ℝ)+2)^d*r^j)*r^2 ≤ D := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,pow_add,mul_assoc] using hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  have he : (2^ε)^j = ((2 : ℝ)^j)^ε := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  have he' : r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε) = 1 := by
    rw [← he]
    dsimp [r]
    rw [inv_pow,inv_pow]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ (2^ε)^2*((2 : ℝ)^j)^ε)
  have he'' : ((j : ℝ)+2)^d*r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε) = ((j : ℝ)+2)^d := by
    calc
      _ = ((j : ℝ)+2)^d*(r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε)) := by ring
      _ = _ := by rw [he',mul_one]
  rw [he''] at hmul
  exact hmul.trans_eq (by ring)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PoissonBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson numerical estimates and local-to-global sieve bounds. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finiteCubicBound_split (S H : Finset Eisenstein) (p : Eisenstein → Prop)
    (hS : ∀ a ∈ S, primary a) (hH : ∀ b ∈ H, primary b) :
    finiteCubicBound S H ≤ finiteCubicBound (S.filter p) H +
      finiteCubicBound (S.filter (fun a => ¬p a)) H := by
  have he : S = (Finset.univ : Finset Bool).biUnion (fun b => S.filter (fun a => if b then p a else ¬p a)) := by
    ext a; simp; tauto
  rw [finiteCubicBound_symm S H hS hH]
  have hh := finiteCubicBound_biUnion (Finset.univ : Finset Bool) H
    (fun b => S.filter (fun a => if b then p a else ¬p a))
  rw [← he] at hh
  have ht := finiteCubicBound_symm H (S.filter p) hH (fun a ha => hS a (Finset.mem_filter.mp ha).1)
  have hf := finiteCubicBound_symm H (S.filter (fun a => ¬p a)) hH
    (fun a ha => hS a (Finset.mem_filter.mp ha).1)
  simpa [Fintype.sum_bool,ht,hf,add_comm] using hh

lemma finiteCubicBound_base_dyad (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ),
      0 < M → 0 < N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ 2*N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*N^ε*(M+N^2) := by
  obtain ⟨C,hC,hbound⟩ := finiteCubicBound_base_thin ε hε
  refine ⟨C+2*C*(Real.sqrt 2)^ε,by positivity,?_⟩
  intro S H M N hM hN hS hH
  let S₀ := S.filter (fun a => norm a ≤ Real.sqrt 2*N)
  let S₁ := S.filter (fun a => ¬norm a ≤ Real.sqrt 2*N)
  have hS₀ : ∀ a ∈ S₀, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N := by
    intro a ha; have hh := Finset.mem_filter.mp ha
    exact ⟨(hS a hh.1).1,(hS a hh.1).2.1,(hS a hh.1).2.2.1,hh.2⟩
  have hS₁ : ∀ a ∈ S₁, primary a ∧ Squarefree a ∧ Real.sqrt 2*N ≤ norm a ∧ norm a ≤ Real.sqrt 2*(Real.sqrt 2*N) := by
    intro a ha; have hh := Finset.mem_filter.mp ha
    refine ⟨(hS a hh.1).1,(hS a hh.1).2.1,le_of_not_ge hh.2,?_⟩
    have he : Real.sqrt 2*(Real.sqrt 2*N) = 2*N := by rw [← mul_assoc,Real.mul_self_sqrt (by norm_num)]
    rw [he]; exact (hS a hh.1).2.2.2
  have h0 := hbound S₀ H M N hM hN hS₀ hH
  have h1 := hbound S₁ H M (Real.sqrt 2*N) hM (by positivity) hS₁ hH
  have hsq : (Real.sqrt 2*N)^2 = 2*N^2 := by rw [mul_pow,Real.sq_sqrt (by norm_num)]
  rw [Real.mul_rpow (Real.sqrt_nonneg _) hN.le,hsq] at h1
  have hsplit := finiteCubicBound_split S H (fun a => norm a ≤ Real.sqrt 2*N)
    (fun a ha => (hS a ha).1) (fun x hx => (hH x hx).1)
  have hnon : 0 ≤ C*(Real.sqrt 2)^ε*N^ε*M := by positivity
  dsimp only [S₀,S₁] at h0 h1
  nlinarith

lemma finiteCubicBound_base_global (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ),
      1 ≤ M → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*N^ε*(M+N^2) := by
  obtain ⟨C,hC,hbound⟩ := finiteCubicBound_base_dyad (ε/2) (by linarith)
  obtain ⟨D,hD,hpoly⟩ := dyadic_polynomial_small_power 1 (show 0 < ε/2 by linarith)
  refine ⟨C*D,by positivity,?_⟩
  intro S H M N hM hN hS hH
  let L := Nat.log 2 ⌊N⌋₊
  let R : ℕ → Finset Eisenstein := fun j => S.filter (fun a => Nat.log 2 (normNat a) = j)
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hfloor : ⌊N⌋₊ ≠ 0 := by
    have hh : (1 : ℕ) ≤ ⌊N⌋₊ := by apply Nat.le_floor; simpa using hN
    omega
  have hpow : (2 : ℝ)^L ≤ N := by
    have h := Nat.pow_log_le_self 2 hfloor
    have hr : (2 : ℝ)^L ≤ (⌊N⌋₊ : ℝ) := by exact_mod_cast h
    exact hr.trans (Nat.floor_le hN0.le)
  have hcover : S ⊆ (Finset.range (L+1)).biUnion R := by
    intro a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 (normNat a),Finset.mem_range.mpr ?_,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩
    have hn : normNat a ≤ ⌊N⌋₊ := Nat.le_floor (by rw [normNat_cast]; exact (hS a ha).2.2)
    have hl : Nat.log 2 (normNat a) ≤ L := Nat.log_mono_right hn
    omega
  have hR (j : ℕ) : ∀ a ∈ R j, primary a ∧ Squarefree a ∧ (2 : ℝ)^j ≤ norm a ∧ norm a ≤ 2*(2 : ℝ)^j := by
    intro a ha
    have hh := Finset.mem_filter.mp ha
    have hfreq := frequencyDyad_norm (mem_frequencyDyad.mpr ⟨primary_ne_zero (hS a hh.1).1,hh.2⟩)
    exact ⟨(hS a hh.1).1,(hS a hh.1).2.1,hfreq⟩
  have hterm (j : ℕ) (hj : j ∈ Finset.range (L+1)) :
      finiteCubicBound H (R j) ≤ C*N^(ε/2)*(M+N^2) := by
    rw [finiteCubicBound_symm H _ (fun x hx => (hH x hx).1) (fun a ha => (hR j a ha).1)]
    apply (hbound (R j) H M ((2 : ℝ)^j) hM0 (by positivity) (hR j) hH).trans
    have hjL : j ≤ L := by have : j < L+1 := Finset.mem_range.mp hj; omega
    have hpowj : (2 : ℝ)^j ≤ N := (pow_le_pow_right₀ (by norm_num) hjL).trans hpow
    gcongr
  have hcount : (L+1 : ℝ) ≤ D*N^(ε/2) := by
    have hh := hpoly L
    simp only [pow_one] at hh
    have hp : D*((2 : ℝ)^L)^(ε/2) ≤ D*N^(ε/2) := by gcongr
    linarith
  calc
    _ = finiteCubicBound H S := finiteCubicBound_symm S H (fun a ha => (hS a ha).1) (fun x hx => (hH x hx).1)
    _ ≤ finiteCubicBound H ((Finset.range (L+1)).biUnion R) := finiteCubicBound_mono (Finset.Subset.refl H) hcover
    _ ≤ ∑ j ∈ Finset.range (L+1), finiteCubicBound H (R j) := finiteCubicBound_biUnion _ _ _
    _ ≤ (L+1 : ℝ)*(C*N^(ε/2)*(M+N^2)) := by
      have h := Finset.sum_le_card_nsmul _ _ _ hterm
      simpa only [Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using h
    _ ≤ (D*N^(ε/2))*(C*N^(ε/2)*(M+N^2)) := by gcongr
    _ = C*D*N^ε*(M+N^2) := by
      have he : N^(ε/2)*N^(ε/2) = N^ε := by rw [← Real.rpow_add hN0]; congr 1; ring
      calc
        _ = C*D*(N^(ε/2)*N^(ε/2))*(M+N^2) := by ring
        _ = _ := by rw [he]

theorem sieveExponent_two : SieveExponent 2 := by
  intro ε hε
  obtain ⟨C,hC,hbase⟩ := finiteCubicBound_base_global ε hε
  refine ⟨C,hC,?_⟩
  intro S H M N hM hN hS hH
  apply (hbase S H M N hM hN hS (fun x hx => ⟨(hH x hx).1,(hH x hx).2.2⟩)).trans
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have he : M+N^2 ≤ M+(M*N)^(2/3 : ℝ)+N^(2 : ℝ) := by
    rw [Real.rpow_two]
    have : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
    linarith
  have hn : N ≤ M*N := le_mul_of_one_le_left hN0 hM
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0 hn hε.le) hC.le)
    he (by positivity) (by positivity)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_QuantitativeRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform quantitative recurrence and exponent monotonicity. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sieveRecurrenceShape_nonneg {ξ M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    0 ≤ sieveRecurrenceShape ξ M N := by unfold sieveRecurrenceShape; positivity

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma SieveExponent.mono {ξ ζ : ℝ} (hξ : SieveExponent ξ) (h : ξ ≤ ζ) : SieveExponent ζ := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := hξ ε hε
  refine ⟨C,hC,?_⟩
  intro S H M N hM hN hS hH
  exact (hbound S H M N hM hN hS hH).trans (by
    gcongr)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveImprovement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification, iteration to exponent four-thirds and the cubic large sieve. -/

section

noncomputable section
namespace CubicFirstMoment

lemma sieveImprove_properties {ξ : ℝ} (hξ : 4/3 ≤ ξ) (_hξ2 : ξ ≤ 2) :
    1 ≤ sieveAmplify ξ ∧ sieveAmplify ξ ≤ 2 ∧
    4/3 ≤ sieveImprove ξ ∧ sieveImprove ξ ≤ ξ ∧
    sieveAmplify ξ ≤ sieveImprove ξ ∧
    (2/3 : ℝ)*(sieveAmplify ξ+1) = sieveImprove ξ ∧
    sieveAmplify ξ*(1-ξ)+2*ξ-1 = sieveImprove ξ ∧
    sieveImprove ξ ≤ 4/3+(2/3 : ℝ)*(ξ-4/3) := by
  have hd : 0 < 3*ξ-1 := by linarith
  unfold sieveAmplify sieveImprove
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr; linarith
  · apply (div_le_iff₀ hd).mpr; linarith
  · apply (le_div_iff₀ hd).mpr; linarith
  · apply (div_le_iff₀ hd).mpr; nlinarith [sq_nonneg (3*ξ-4)]
  · apply div_le_div_of_nonneg_right _ hd.le; linarith
  · field_simp [ne_of_gt hd]; ring
  · apply (eq_div_iff (ne_of_gt hd)).mpr
    have he := div_mul_cancel₀ (6*ξ-5) (ne_of_gt hd)
    nlinarith [congrArg (fun x : ℝ => x*(ξ-1)) he]
  · apply (div_le_iff₀ hd).mpr; nlinarith [sq_nonneg (3*ξ-4)]

lemma sieve_amplification_numerical {ξ M N : ℝ} (hξ : 4/3 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hN : 1 ≤ N) (hNM : N ≤ M) :
    sieveRecurrenceShape ξ (max M (N^sieveAmplify ξ)) N ≤
      4*(M+(M*N)^(2/3 : ℝ)+N^sieveImprove ξ) := by
  obtain ⟨ha,ha2,hf,hfξ,haf,hafid,herrid,hcon⟩ := sieveImprove_properties hξ hξ2
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := hN0.trans_le hNM
  have hP : 0 < max M (N^sieveAmplify ξ) := hM0.trans_le (le_max_left _ _)
  have hfirst : max M (N^sieveAmplify ξ) ≤ M+N^sieveImprove ξ := by
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · exact (Real.rpow_le_rpow_of_exponent_le hN haf).trans (le_add_of_nonneg_left hM0.le)
  have hmixed : (max M (N^sieveAmplify ξ)*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ)+N^sieveImprove ξ := by
    rw [max_mul_of_nonneg _ _ hN0.le,Real.rpow_max (by positivity) (by positivity) (by norm_num)]
    have he : (N^sieveAmplify ξ*N)^(2/3 : ℝ) = N^sieveImprove ξ := by
      rw [← Real.rpow_add_one hN0.ne',← Real.rpow_mul hN0.le]
      congr 1
      nlinarith [hafid]
    rw [he]
    exact max_le_add_of_nonneg (by positivity) (by positivity)
  have herr : (max M (N^sieveAmplify ξ))^(1-ξ)*N^(2*ξ-1) ≤ N^sieveImprove ξ := by
    calc
      _ ≤ (N^sieveAmplify ξ)^(1-ξ)*N^(2*ξ-1) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (by positivity)
          (le_max_right _ _) (by linarith)) (by positivity)
      _ = N^sieveImprove ξ := by
        rw [← Real.rpow_mul hN0.le,← Real.rpow_add hN0]
        congr 1
        linarith
  have hNf : N ≤ N^sieveImprove ξ := by
    calc
      _ = N^(1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hmix0 : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
  unfold sieveRecurrenceShape
  linarith

lemma sieve_amplification_size {ξ M N : ℝ} (hξ : 4/3 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hN : 1 ≤ N) (hNM : N ≤ M) :
    max M (N^sieveAmplify ξ)*N ≤ (M*N)^2 := by
  have hM1 : 1 ≤ M := hN.trans hNM
  have hN0 : 0 ≤ N := (zero_lt_one.trans_le hN).le
  have hM0 : 0 ≤ M := (zero_lt_one.trans_le hM1).le
  have ha2 := (sieveImprove_properties hξ hξ2).2.1
  have hp : max M (N^sieveAmplify ξ) ≤ M^2 := by
    apply max_le
    · nlinarith
    · calc
        _ ≤ N^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN ha2
        _ = N^2 := Real.rpow_two _
        _ ≤ M^2 := by gcongr
  calc
    _ ≤ M^2*N := mul_le_mul_of_nonneg_right hp hN0
    _ ≤ (M*N)^2 := by nlinarith [mul_nonneg (sq_nonneg M) (show 0 ≤ N^2-N by nlinarith)]

end CubicFirstMoment
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma SieveExponent.improve {ξ : ℝ} (hξ : 4/3 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) : SieveExponent (sieveImprove ξ) := by
  intro ε hε
  obtain ⟨C,hC,hrec⟩ := hExp.recurrence (by linarith : 1 ≤ ξ) hξ2 (half_pos hε)
  have hf : 1 ≤ sieveImprove ξ := by have := (sieveImprove_properties hξ hξ2).2.2.1; linarith
  have hordered : ∀ S H : Finset Eisenstein, ∀ M N : ℝ, 1 ≤ N → N ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ b ∈ H, primary b ∧ Squarefree b ∧ norm b ≤ M) →
      finiteCubicBound S H ≤ (4*C)*(M*N)^ε*(M+(M*N)^(2/3 : ℝ)+N^sieveImprove ξ) := by
    intro S H M N hN hNM hS hH
    let P : ℝ := max M (N^sieveAmplify ξ)
    have hMP : M ≤ P := le_max_left _ _
    have hNP : N ≤ P := hNM.trans hMP
    have hM0 : 0 < M := (zero_lt_one.trans_le hN).trans_le hNM
    have hN0 : 0 < N := zero_lt_one.trans_le hN
    have hP0 : 0 < P := hM0.trans_le hMP
    have hb := hrec S H P N hN hNP hS (fun b hb => ⟨(hH b hb).1,(hH b hb).2.2.trans hMP⟩)
    have hp : (P*N)^(ε/2) ≤ (M*N)^ε := by
      calc
        _ ≤ ((M*N)^2)^(ε/2) := Real.rpow_le_rpow (by positivity)
          (sieve_amplification_size hξ hξ2 hN hNM) (half_pos hε).le
        _ = (M*N)^ε := by
          rw [← Real.rpow_natCast_mul (by positivity)]
          congr 1
          ring
    have hs := sieve_amplification_numerical hξ hξ2 hN hNM
    exact hb.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hs
      (sieveRecurrenceShape_nonneg hP0.le hN0.le) (by positivity)).trans_eq (by ring))
  refine ⟨8*C,by positivity,?_⟩
  intro S H M N hM hN hS hH
  have hM0 : 0 ≤ M := (zero_lt_one.trans_le hM).le
  have hN0 : 0 ≤ N := (zero_lt_one.trans_le hN).le
  by_cases hNM : N ≤ M
  · exact (hordered S H M N hN hNM hS hH).trans (by gcongr; linarith)
  · have hMN : M ≤ N := le_of_not_ge hNM
    rw [finiteCubicBound_symm S H (fun a ha => (hS a ha).1) (fun b hb => (hH b hb).1)]
    have hb := hordered H S N M hM hMN hH hS
    have hNpow : N ≤ N^sieveImprove ξ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN hf
    have hMpow : M^sieveImprove ξ ≤ N^sieveImprove ξ := Real.rpow_le_rpow hM0 hMN (by linarith)
    have hs : N+(M*N)^(2/3 : ℝ)+M^sieveImprove ξ ≤
        2*(M+(M*N)^(2/3 : ℝ)+N^sieveImprove ξ) := by
      have hp : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
      linarith
    rw [mul_comm N M] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring))

lemma SieveExponent.contract {ξ : ℝ} (hξ : 4/3 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) : SieveExponent (4/3+(2/3 : ℝ)*(ξ-4/3)) :=
  (hExp.improve hξ hξ2).mono (sieveImprove_properties hξ hξ2).2.2.2.2.2.2.2

end CubicFirstMoment
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sieveExponent_approach (n : ℕ) : SieveExponent (4/3+(2/3 : ℝ)^(n+1)) := by
  induction n with
  | zero => convert sieveExponent_two using 1; norm_num
  | succ n ih =>
    have hl : (4/3 : ℝ) ≤ 4/3+(2/3 : ℝ)^(n+1) := le_add_of_nonneg_right (by positivity)
    have hu : 4/3+(2/3 : ℝ)^(n+1) ≤ 2 := by
      have hh' : (2/3 : ℝ)^(n+1) ≤ 2/3 := by
        rw [pow_succ]
        exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (n := n) (by norm_num) (by norm_num))
      linarith
    convert ih.contract hl hu using 1
    all_goals try with_reducible_and_instances rfl
    simp only [pow_succ]
    ring

theorem sieveExponent_four_thirds_oai : SieveExponent (4/3) := by
  intro ε hε
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (2/3 : ℝ) < 1)
  have hn' : (2/3 : ℝ)^(n+1) ≤ ε/2 := by
    rw [pow_succ]
    exact (mul_le_of_le_one_right (by positivity) (by norm_num : (2/3 : ℝ) ≤ 1)).trans hn.le
  obtain ⟨C,hC,hbound⟩ := sieveExponent_approach n (ε/2) (half_pos hε)
  refine ⟨C,hC,?_⟩
  intro S H M N hM hN hS hH
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hMN : 1 ≤ M*N := one_le_mul_of_one_le_of_one_le hM hN
  have hNmn : N ≤ M*N := le_mul_of_one_le_left hN0.le hM
  have hpow1 : 1 ≤ (M*N)^(ε/2) := Real.one_le_rpow hMN (half_pos hε).le
  have hnpow : N^(4/3+(2/3 : ℝ)^(n+1)) ≤ (M*N)^(ε/2)*N^(4/3 : ℝ) := by
    calc
      _ ≤ N^(4/3+ε/2) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = N^(ε/2)*N^(4/3 : ℝ) := by rw [Real.rpow_add hN0]; ring
      _ ≤ _ := by gcongr
  have hm : M ≤ (M*N)^(ε/2)*M := le_mul_of_one_le_left hM0.le hpow1
  have hmix : (M*N)^(2/3 : ℝ) ≤ (M*N)^(ε/2)*(M*N)^(2/3 : ℝ) := le_mul_of_one_le_left (by positivity) hpow1
  have hs : M+(M*N)^(2/3 : ℝ)+N^(4/3+(2/3 : ℝ)^(n+1)) ≤
      (M*N)^(ε/2)*(M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ)) := by nlinarith
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+(M*N)^(2/3 : ℝ)+N^(4/3+(2/3 : ℝ)^(n+1))) := hbound S H M N hM hN hS hH
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ))) := by gcongr
    _ = C*(M*N)^ε*(M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ)) := by
      have he : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add (by positivity),show ε/2+ε/2 = ε by ring]
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ)) := by ring
        _ = _ := by rw [he]

end CubicFirstMoment
end
end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.sieveExponent_four_thirds_oai := @OAI.CubicFirstMoment.sieveExponent_four_thirds_oai
