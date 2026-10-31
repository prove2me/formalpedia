-- Prove2me | solution 1 for OAI.CubicFirstMoment.SieveExponent.recurrence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:57:53.016362+00:00
-- url     : https://prove2.me/submissions/b5aeb5b6-68a0-4876-b332-bab068ec0434

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022

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
-- module Solutions.OAIQ096_CM.CubicGram_CubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary cube decomposition and finite operator block bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finiteCubicBound_twist_controls_mass (P S : Finset Eisenstein)
    (u z : Eisenstein → ℂ) (hz : ∀ b ∈ P, ‖z b‖ ≤ 1) :
    (∑ s ∈ S, ‖∑ b ∈ P, u b*z b*cubicSymbol b s‖^2) ≤
      finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 := by
  apply (finiteCubicBound_controls_mass P S (fun b => u b*z b)).trans
  apply mul_le_mul_of_nonneg_left _ (finiteCubicBound_nonneg _ _)
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul, mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) (by
    simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (hz b hb) 2)

lemma finiteCubicBound_twist_conjugate_mass (P S : Finset Eisenstein)
    (u z : Eisenstein → ℂ) (hz : ∀ b ∈ P, ‖z b‖ ≤ 1) :
    (∑ s ∈ S, ‖∑ b ∈ P, u b*z b*star (cubicSymbol b s)‖^2) ≤
      finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 := by
  have h := finiteCubicBound_twist_controls_mass P S (fun b => star (u b))
    (fun b => star (z b)) (fun b hb => by simpa using hz b hb)
  have he (s : Eisenstein) :
      (∑ b ∈ P, u b*z b*star (cubicSymbol b s)) =
      star (∑ b ∈ P, star (u b)*star (z b)*cubicSymbol b s) := by
    simp [star_sum, star_mul, mul_comm, mul_assoc]
  simpa only [he, norm_star] using h

end CubicFirstMoment

namespace CubicFirstMoment

lemma cubeBlockMass_le_first (P S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (u : Eisenstein → ℂ) :
    cubeBlockMass P S T C u ≤
      (T.card : ℝ) * C.card * finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 := by
  have hrow (t c : Eisenstein) :
      (∑ s ∈ S, ‖∑ b ∈ P, u b * cubicSymbol b (s*t^2*c^3)‖^2) ≤
      finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 := by
    have h := finiteCubicBound_twist_controls_mass P S u
      (fun b => cubicSymbol b (t^2*c^3)) (fun b hb => norm_cubicSymbol_le_one (hP b hb) _)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro s hs
    congr 2
    apply Finset.sum_congr rfl
    intro b hb
    rw [mul_assoc s, cubicSymbol_mul_upper (hP b hb)]
    ring
  unfold cubeBlockMass
  rw [Finset.sum_comm (s := S) (t := T)]
  simp_rw [Finset.sum_comm (s := S) (t := C)]
  calc
    _ ≤ ∑ t ∈ T, ∑ c ∈ C, finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun c _ => hrow t c))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

lemma cubeBlockMass_le_second (P S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (u : Eisenstein → ℂ) :
    cubeBlockMass P S T C u ≤
      (S.card : ℝ) * C.card * finiteCubicBound P T * ∑ b ∈ P, ‖u b‖^2 := by
  have hrow (s c : Eisenstein) :
      (∑ t ∈ T, ‖∑ b ∈ P, u b * cubicSymbol b (s*t^2*c^3)‖^2) ≤
      finiteCubicBound P T * ∑ b ∈ P, ‖u b‖^2 := by
    have h := finiteCubicBound_twist_conjugate_mass P T u
      (fun b => cubicSymbol b (s*c^3)) (fun b hb => norm_cubicSymbol_le_one (hP b hb) _)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro t ht
    congr 2
    apply Finset.sum_congr rfl
    intro b hb
    rw [cubicSymbol_mul_upper (hP b hb), cubicSymbol_mul_upper (hP b hb),
      cubicSymbol_mul_upper (hP b hb), cubicSymbol_pow_upper (hP b hb),
      cubicSymbol_sq_eq_star (hP b hb)]
    ring
  unfold cubeBlockMass
  simp_rw [Finset.sum_comm (s := T) (t := C)]
  calc
    _ ≤ ∑ s ∈ S, ∑ c ∈ C, finiteCubicBound P T * ∑ b ∈ P, ‖u b‖^2 :=
      Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun c _ => hrow s c))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem cubeBlockMass_le_min (P S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (u : Eisenstein → ℂ) :
    cubeBlockMass P S T C u ≤
      min ((T.card : ℝ) * C.card * finiteCubicBound P S)
          ((S.card : ℝ) * C.card * finiteCubicBound P T) * ∑ b ∈ P, ‖u b‖^2 := by
  rw [min_mul_of_nonneg _ _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact le_min (cubeBlockMass_le_first P S T C hP u) (cubeBlockMass_le_second P S T C hP u)

end CubicFirstMoment

namespace CubicFirstMoment

lemma cubeBlockSupport_mass_le (P S T C : Finset Eisenstein) (u : Eisenstein → ℂ) :
    (∑ n ∈ cubeBlockSupport S T C, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
      cubeBlockMass P S T C u := by
  calc
    _ ≤ ∑ z ∈ S.product (T.product C),
        ‖∑ b ∈ P, u b*cubicSymbol b (z.1*z.2.1^2*z.2.2^3)‖^2 :=
      Finset.sum_image_le_of_nonneg
        (s := S.product (T.product C)) (g := fun z => z.1*z.2.1^2*z.2.2^3)
        (f := fun n => ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) (fun _ _ => sq_nonneg _)
    _ = _ := by
      unfold cubeBlockMass
      exact (Finset.sum_product S (T.product C) _).trans
        (Finset.sum_congr rfl (fun s _ => Finset.sum_product T C _))

theorem finiteCubicBound_cubeBlock (P S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) :
    finiteCubicBound P (cubeBlockSupport S T C) ≤
      min ((T.card : ℝ) * C.card * finiteCubicBound P S)
          ((S.card : ℝ) * C.card * finiteCubicBound P T) := by
  apply (finiteCubicBound_le_iff _ _ (le_min
    (mul_nonneg (by positivity) (finiteCubicBound_nonneg P S))
    (mul_nonneg (by positivity) (finiteCubicBound_nonneg P T)))).mpr
  intro u
  exact (cubeBlockSupport_mass_le P S T C u).trans (cubeBlockMass_le_min P S T C hP u)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma residualCubeSupport_mass_le (P R S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (u : Eisenstein → ℂ) :
    (∑ n ∈ residualCubeSupport R S T C, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
      (R.card : ℝ) *
        min ((T.card : ℝ)*C.card*finiteCubicBound P S)
            ((S.card : ℝ)*C.card*finiteCubicBound P T) * ∑ b ∈ P, ‖u b‖^2 := by
  let L := min ((T.card : ℝ)*C.card*finiteCubicBound P S)
    ((S.card : ℝ)*C.card*finiteCubicBound P T)
  have htw (r : Eisenstein) :
      (∑ n ∈ (cubeBlockSupport S T C).image (r * ·), ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
        L * ∑ b ∈ P, ‖u b‖^2 := by
    have h := finiteCubicBound_twist_controls_mass P (cubeBlockSupport S T C) u
      (fun b => cubicSymbol b r) (fun b hb => norm_cubicSymbol_le_one (hP b hb) r)
    calc
      _ ≤ ∑ n ∈ cubeBlockSupport S T C, ‖∑ b ∈ P, u b*cubicSymbol b (r*n)‖^2 :=
        Finset.sum_image_le_of_nonneg (g := fun n => r*n)
          (f := fun n => ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) (fun _ _ => sq_nonneg _)
      _ = ∑ n ∈ cubeBlockSupport S T C, ‖∑ b ∈ P, u b*cubicSymbol b r*cubicSymbol b n‖^2 := by
        apply Finset.sum_congr rfl; intro n hn
        congr 2
        apply Finset.sum_congr rfl; intro b hb
        rw [cubicSymbol_mul_upper (hP b hb)]; ring
      _ ≤ finiteCubicBound P (cubeBlockSupport S T C) * ∑ b ∈ P, ‖u b‖^2 := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (finiteCubicBound_cubeBlock P S T C hP)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hunion : (∑ n ∈ residualCubeSupport R S T C, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
      ∑ r ∈ R, ∑ n ∈ (cubeBlockSupport S T C).image (r * ·),
        ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := by
    classical
    induction R using Finset.induction_on with
    | empty => simp [residualCubeSupport]
    | @insert r R hr ih =>
      rw [residualCubeSupport, Finset.biUnion_insert, Finset.sum_insert hr]
      dsimp only [residualCubeSupport] at ih
      have hh : ∀ n ∈ (cubeBlockSupport S T C).image (r * ·) ∩
          R.biUnion (fun r => (cubeBlockSupport S T C).image (r * ·)),
          (0 : ℝ) ≤ ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := fun _ _ => sq_nonneg _
      have he := Finset.sum_union_inter (s₁ := (cubeBlockSupport S T C).image (r * ·))
        (s₂ := R.biUnion (fun r => (cubeBlockSupport S T C).image (r * ·)))
        (f := fun n => ‖∑ b ∈ P, u b*cubicSymbol b n‖^2)
      have hn := Finset.sum_nonneg hh
      linarith
  calc
    _ ≤ ∑ r ∈ R, ∑ n ∈ (cubeBlockSupport S T C).image (r * ·),
        ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := hunion
    _ ≤ ∑ r ∈ R, L * ∑ b ∈ P, ‖u b‖^2 := Finset.sum_le_sum (fun r _ => htw r)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem finiteCubicBound_residualCube (P R S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) :
    finiteCubicBound P (residualCubeSupport R S T C) ≤
      (R.card : ℝ) * min ((T.card : ℝ)*C.card*finiteCubicBound P S)
          ((S.card : ℝ)*C.card*finiteCubicBound P T) := by
  apply (finiteCubicBound_le_iff _ _ (mul_nonneg (by positivity)
    (le_min (by positivity [finiteCubicBound_nonneg P S])
      (by positivity [finiteCubicBound_nonneg P T])))).mpr
  exact residualCubeSupport_mass_le P R S T C hP

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

lemma geometric_decay_step {q d : ℝ} (hq : 1 < q) (hd : 0 < d) (j : ℕ) :
    q^j/(1+d*q^j)^2 ≤
      (q/(d*(q-1)))*(1/(1+d*q^j)-1/(1+d*q^(j+1))) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have ht : 0 < q^j := by positivity
  have h1 : 0 < 1+d*q^j := by positivity
  have h2 : 0 < 1+d*q^j*q := by positivity
  have hdq : 0 < d*(q-1) := by positivity
  have he : (q/(d*(q-1)))*(1/(1+d*q^j)-1/(1+d*q^(j+1))) =
      q*q^j/((1+d*q^j)*(1+d*q^j*q)) := by
    rw [pow_succ]
    have hqm : q-1 ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
  have ht' : 0 ≤ q^j*(1+d*q^j) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hq.le) ht']

lemma geometric_decay_partial_sum {q d : ℝ} (hq : 1 < q) (hd : 0 < d) (n : ℕ) :
    (∑ j ∈ Finset.range n, q^j/(1+d*q^j)^2) ≤ q/(d*(q-1)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => geometric_decay_step hq hd j)
  rw [← Finset.mul_sum] at h
  have ht : (∑ j ∈ Finset.range n, (1/(1+d*q^j)-1/(1+d*q^(j+1)))) =
      1/(1+d) - 1/(1+d*q^n) := by
    have hh := Finset.sum_range_sub (fun j => (1 : ℝ)/(1+d*q^j)) n
    rw [Finset.sum_sub_distrib] at hh ⊢
    simp only [pow_zero,mul_one] at hh
    linarith
  rw [ht] at h
  have hdq : 0 ≤ q/(d*(q-1)) := by positivity
  have hfirst : 1/(1+d) ≤ (1 : ℝ) := (div_le_one (by positivity)).mpr (by linarith)
  have hlast : (0 : ℝ) ≤ 1/(1+d*q^n) := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left (by linarith : 1/(1+d)-1/(1+d*q^n) ≤ 1) hdq).trans_eq (mul_one _))

lemma geometric_decay_tsum {q d : ℝ} (hq : 1 < q) (hd : 0 < d) :
    Summable (fun j : ℕ => q^j/(1+d*q^j)^2) ∧
      (∑' j : ℕ, q^j/(1+d*q^j)^2) ≤ q/(d*(q-1)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hs := summable_of_sum_range_le (fun j => by positivity : ∀ j : ℕ, 0 ≤ q^j/(1+d*q^j)^2)
    (geometric_decay_partial_sum hq hd)
  exact ⟨hs,hs.tsum_le_of_sum_range_le (geometric_decay_partial_sum hq hd)⟩

lemma rpow_cutoff_comparison {α x : ℝ} (hα : 0 < α) (hα4 : α ≤ 4) (hx : 0 ≤ x) :
    (1+x^α)^2 ≤ 4*(1+x)^8 := by
  by_cases hx1 : x ≤ 1
  · have hp := Real.rpow_le_rpow hx hx1 hα.le
    rw [Real.one_rpow] at hp
    have hn := Real.rpow_nonneg hx α
    have hb : 1 ≤ (1+x)^8 := one_le_pow₀ (by linarith)
    nlinarith
  · have hx1 : 1 ≤ x := le_of_not_ge hx1
    have hp : x^α ≤ x^4 := by simpa using Real.rpow_le_rpow_of_exponent_le hx1 hα4
    have hn := Real.rpow_nonneg hx α
    have he : (1+x^α)^2 ≤ (1+x^4)^2 := by gcongr
    have hpow : 1+x^4 ≤ (1+x)^4 := by simpa using pow_add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hx (by norm_num : (4 : ℕ) ≠ 0)
    have he' : (1+x^4)^2 ≤ (1+x)^8 := by
      have := pow_le_pow_left₀ (by positivity) hpow 2
      simpa only [← pow_mul] using this
    have hb : 0 ≤ (1+x)^8 := by positivity
    linarith

lemma real_dyadic_decay (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 4) {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α/(1+c*2^j)^8) ∧
      (∑' j : ℕ, ((2 : ℝ)^j)^α/(1+c*2^j)^8) ≤
        (4*2^α/(2^α-1))*c^(-α) := by
  have hq : (1 : ℝ) < 2^α := Real.one_lt_rpow (by norm_num) hα
  have hd : 0 < c^α := Real.rpow_pos_of_pos hc α
  have he (j : ℕ) : ((2 : ℝ)^j)^α = (2^α)^j := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  have hmajor (j : ℕ) : ((2 : ℝ)^j)^α/(1+c*2^j)^8 ≤
      4*((2^α)^j/(1+c^α*(2^α)^j)^2) := by
    have hnum : 0 ≤ ((2 : ℝ)^j)^α := by positivity
    have hi : (1+(c*2^j)^α)^2 ≤ 4*(1+c*2^j)^8 := rpow_cutoff_comparison hα hα4 (by positivity)
    rw [Real.mul_rpow hc.le (by positivity),he] at hi
    rw [he]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < (1+c*2^j)^8)
      (by positivity : 0 < (1+c^α*(2^α)^j)^2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ (2^α)^j by positivity)]
  have hs := (geometric_decay_tsum hq hd).1.mul_left 4
  have hs' := hs.of_nonneg_of_le (fun _ => by positivity) hmajor
  refine ⟨hs',?_⟩
  calc
    _ ≤ ∑' j : ℕ, 4*((2^α)^j/(1+c^α*(2^α)^j)^2) := hs'.tsum_le_tsum hmajor hs
    _ = 4*∑' j : ℕ, (2^α)^j/(1+c^α*(2^α)^j)^2 := tsum_mul_left
    _ ≤ 4*(2^α/(c^α*(2^α-1))) := mul_le_mul_of_nonneg_left (geometric_decay_tsum hq hd).2 (by norm_num)
    _ = _ := by rw [Real.rpow_neg hc.le]; field_simp

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_squarefreePrimaryDyad {n : Eisenstein} {j : ℕ} :
    n ∈ squarefreePrimaryDyad j ↔ n ∈ frequencyDyad j ∧ primary n ∧ Squarefree n := by
  simp [squarefreePrimaryDyad]

lemma mem_cubeDyadTriples {j i t c : ℕ} :
    (i,t,c) ∈ cubeDyadTriples j ↔ i+2*t+3*c ≤ j+1 := by
  simp [cubeDyadTriples,Finset.mem_product,Finset.mem_range]
  omega

lemma cubeDyadTriples_card (j : ℕ) : (cubeDyadTriples j).card ≤ (j+2)^3 := by
  have h := Finset.card_filter_le (s := (Finset.range (j+2)).product
    ((Finset.range (j+2)).product (Finset.range (j+2))))
    (p := fun z : ℕ×ℕ×ℕ => z.1+2*z.2.1+3*z.2.2 ≤ j+1)
  simpa [cubeDyadTriples,Finset.card_product,Finset.card_range,pow_succ,mul_assoc] using h

lemma frequencyDyad_subset_cubeCover (j : ℕ) : frequencyDyad j ⊆ cubeFrequencyCover j := by
  intro n hn
  obtain ⟨r,s,t,c,hr0,hr,hs,ht,hss,hst,hcop,hc0,he⟩ :=
    full_cube_decomposition (mem_frequencyDyad.mp hn).1
  let i := Nat.log 2 (normNat s)
  let l := Nat.log 2 (normNat t)
  let k := Nat.log 2 (normNat c)
  have hsi : s ∈ frequencyDyad i := mem_frequencyDyad.mpr ⟨primary_ne_zero hs,rfl⟩
  have htl : t ∈ frequencyDyad l := mem_frequencyDyad.mpr ⟨primary_ne_zero ht,rfl⟩
  have hck : c ∈ frequencyDyad k := mem_frequencyDyad.mpr ⟨hc0,rfl⟩
  have hprod : (2 : ℝ)^i*((2 : ℝ)^l)^2*((2 : ℝ)^k)^3 ≤ norm n := by
    calc
      _ ≤ norm s*(norm t)^2*(norm c)^3 := by
        have hsn := norm_nonneg s
        have htn := norm_nonneg t
        have hcn := norm_nonneg c
        gcongr <;> exact (frequencyDyad_norm ‹_›).1
      _ ≤ norm r*norm s*(norm t)^2*(norm c)^3 := by
        have hsn := norm_nonneg s
        have hcn := norm_nonneg c
        have hprim : 0 ≤ norm s*(norm t)^2*(norm c)^3 := by positivity [norm_nonneg s]
        have hmul := le_mul_of_one_le_left hprim (one_le_norm hr0)
        nlinarith
      _ = norm n := by rw [he]; simp only [norm_mul_eq,eisenstein_norm_pow]
  have hexp : i+2*l+3*k ≤ j+1 := by
    apply (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
    have heq : (2 : ℝ)^(i+2*l+3*k) = 2^i*(2^l)^2*(2^k)^3 := by
      simp only [pow_add,pow_mul,mul_comm 2 l,mul_comm 3 k]
    rw [heq]
    exact hprod.trans ((frequencyDyad_norm hn).2.trans_eq (by rw [pow_succ]; ring))
  apply Finset.mem_biUnion.mpr
  refine ⟨(i,l,k),mem_cubeDyadTriples.mpr hexp,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r,mem_nonzeroNormBall.mpr ⟨hr,hr0⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨s*t^2*c^3,Finset.mem_image.mpr ⟨(s,t,c),?_ ,rfl⟩,?_⟩
  · exact Finset.mem_product.mpr ⟨mem_squarefreePrimaryDyad.mpr ⟨hsi,hs,hss⟩,
      Finset.mem_product.mpr ⟨mem_squarefreePrimaryDyad.mpr ⟨htl,ht,hst⟩,hck⟩⟩
  · rw [he]; ring

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

theorem finiteCubicBound_frequency_cube (P : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (j : ℕ) :
    finiteCubicBound P (frequencyDyad j) ≤
      (nonzeroNormBall 729).card * ∑ z ∈ cubeDyadTriples j,
        min (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card*
               finiteCubicBound P (squarefreePrimaryDyad z.1))
            (((squarefreePrimaryDyad z.1).card : ℝ)*(frequencyDyad z.2.2).card*
               finiteCubicBound P (squarefreePrimaryDyad z.2.1)) := by
  apply (finiteCubicBound_mono (Finset.Subset.refl P) (frequencyDyad_subset_cubeCover j)).trans
  apply (finiteCubicBound_biUnion (cubeDyadTriples j) P _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun z hz => finiteCubicBound_residualCube _ _ _ _ _ hP)

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x^(1/3 : ℝ))^3 = x := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num

lemma rpow_two_thirds_cube {x : ℝ} (hx : 0 ≤ x) : (x^(2/3 : ℝ))^3 = x^2 := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num

lemma cube_block_numerical {S T K N J ξ : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (hK : 1 ≤ K) (hN : 0 ≤ N)
    (hJ : S*T^2*K^3 ≤ J) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    min (K*T*(N+(N*S)^(2/3 : ℝ)+S^ξ))
        (K*S*(N+(N*T)^(2/3 : ℝ)+T^ξ)) ≤
      N*J^(1/3 : ℝ)+(J*N)^(2/3 : ℝ)+J^ξ+J := by
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ0 : 0 ≤ J := (by positivity : 0 ≤ S*T^2*K^3).trans hJ
  have hJξ : 0 ≤ J^ξ := Real.rpow_nonneg hJ0 _
  have hcrossLeft : K*T*(N*S)^(2/3 : ℝ) ≤ (J*N)^(2/3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*T*(N*S)^(2/3 : ℝ))
      (by positivity : 0 ≤ (J*N)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [mul_pow,mul_pow,rpow_two_thirds_cube (by positivity),rpow_two_thirds_cube (by positivity)]
    calc
      _ = S^2*T^3*K^3*N^2 := by ring
      _ ≤ S^2*T^4*K^6*N^2 := by
        have ht : T^3 ≤ T^4 := pow_le_pow_right₀ hT (by norm_num)
        have hk : K^3 ≤ K^6 := pow_le_pow_right₀ hK (by norm_num)
        gcongr
      _ = (S*T^2*K^3*N)^2 := by ring
      _ ≤ _ := by gcongr
  by_cases hST : T ≤ S
  · have hsmall : K*T ≤ J^(1/3 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*T)
        (by positivity : 0 ≤ J^(1/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [rpow_third_cube hJ0]
      calc
        _ = T*T^2*K^3 := by ring
        _ ≤ S*T^2*K^3 := by gcongr
        _ ≤ J := hJ
    have hp : K*T*S^ξ ≤ J^ξ := by
      have hTK : K*T ≤ T^2*K^3 := by
        calc
          _ = T*K := mul_comm _ _
          _ ≤ T^2*K^3 := by
            gcongr
            · nlinarith [sq_nonneg (T-1)]
            · exact (le_self_pow₀ hK (by norm_num : (3 : ℕ) ≠ 0))
      have hTK1 : 1 ≤ T^2*K^3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) (one_le_pow₀ hK)
      have htξ := Real.self_le_rpow_of_one_le hTK1 hξ
      calc
        _ ≤ (T^2*K^3)^ξ*S^ξ := mul_le_mul_of_nonneg_right (hTK.trans htξ) (by positivity)
        _ = (S*T^2*K^3)^ξ := by rw [← Real.mul_rpow (by positivity) hS0]; congr 1; ring
        _ ≤ J^ξ := Real.rpow_le_rpow (by positivity) hJ (by linarith)
    apply (min_le_left _ _).trans
    have hn := mul_le_mul_of_nonneg_right hsmall hN
    nlinarith
  · have hST : S ≤ T := (le_of_not_ge hST)
    have hsmall : K*S ≤ J^(1/3 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*S)
        (by positivity : 0 ≤ J^(1/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [rpow_third_cube hJ0]
      calc
        _ = S*S^2*K^3 := by ring
        _ ≤ S*T^2*K^3 := by gcongr
        _ ≤ J := hJ
    have hc : K*S*(N*T)^(2/3 : ℝ) ≤ (J*N)^(2/3 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*S*(N*T)^(2/3 : ℝ))
        (by positivity : 0 ≤ (J*N)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [mul_pow,mul_pow,rpow_two_thirds_cube (by positivity),rpow_two_thirds_cube (by positivity)]
      have hST2 : S ≤ T^2 := hST.trans (by nlinarith [sq_nonneg (T-1)])
      calc
        _ = S^2*S*T^2*K^3*N^2 := by ring
        _ ≤ S^2*T^2*T^2*K^6*N^2 := by
          have hk : K^3 ≤ K^6 := pow_le_pow_right₀ hK (by norm_num)
          gcongr
        _ = (S*T^2*K^3*N)^2 := by ring
        _ ≤ _ := by gcongr
    have hp : K*S*T^ξ ≤ J := by
      have htξ : T^ξ ≤ T^2 := by simpa using Real.rpow_le_rpow_of_exponent_le hT hξ2
      calc
        _ ≤ K^3*S*T^2 := by
          gcongr
          exact le_self_pow₀ hK (by norm_num : (3 : ℕ) ≠ 0)
        _ = S*T^2*K^3 := by ring
        _ ≤ J := hJ
    apply (min_le_right _ _).trans
    have hn := mul_le_mul_of_nonneg_right hsmall hN
    nlinarith

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

lemma summable_dualDyadicNorm (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) {c : ℝ} (hc : 0 < c) {A : ℕ} (hA : 2 ≤ A) :
    Summable (fun j : ℕ => finiteCubicBound S (frequencyDyad j) / (1+c*2^j)^A) := by
  have hs := (dyadic_decay_summable hc).mul_left (36*(S.card : ℝ))
  apply hs.of_nonneg_of_le
  · intro j
    exact div_nonneg (finiteCubicBound_nonneg _ _) (by positivity)
  · intro j
    have hd : 0 < (1+c*(2 : ℝ)^j)^2 := by positivity
    have hp : (1+c*(2 : ℝ)^j)^2 ≤ (1+c*2^j)^A :=
      pow_le_pow_right₀ (by linarith [show 0 ≤ c*(2 : ℝ)^j by positivity]) hA
    calc
      _ ≤ finiteCubicBound S (frequencyDyad j)/(1+c*2^j)^2 :=
        div_le_div_of_nonneg_left (finiteCubicBound_nonneg _ _) hd hp
      _ ≤ (36*S.card*2^j)/(1+c*2^j)^2 := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact (finiteCubicBound_le_card_mul S _ hS).trans
          ((mul_le_mul_of_nonneg_left (frequencyDyad_card_le j) (by positivity)).trans_eq (by ring))
      _ = _ := by ring

lemma dualDyadicNorm_nonneg (S : Finset Eisenstein) {c : ℝ} (hc : 0 ≤ c) (A : ℕ) :
    0 ≤ dualDyadicNorm S c A :=
  tsum_nonneg (fun j => div_nonneg (finiteCubicBound_nonneg _ _) (by positivity))

theorem coprimeGramForm_norm_recurrence (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) (hA : 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ ¬ IsUnit a) →
      ∀ (u : Eisenstein → ℂ) (Z N : ℝ), 0 < Z → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ‖coprimeGramForm S u W Z‖ ≤ C*(Z/N)*
        dualDyadicNorm S (Z/(27*N^2)) A *
          ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprimePoissonDyad_norm_recurrence W hW hW' A
  refine ⟨C,hC,?_⟩
  intro S hS u Z N hZ hN hSN
  let E : ℝ := ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun a _ => by positivity)
  let c : ℝ := Z/(27*N^2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hterm (j : ℕ) : ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ ≤
      (C*(Z/N)*E)*(finiteCubicBound S (frequencyDyad j)/(1+c*2^j)^A) := by
    have hrec := hbound S (frequencyDyad j) (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
      u Z ((2 : ℝ)^j) N hZ.le (by positivity) hN hSN (fun h hh => frequencyDyad_norm hh)
    have he : Z*2^j/(27*N^2) = c*2^j := by dsimp [c]; ring
    rw [he] at hrec
    calc
      _ ≤ C*(Z/N)*finiteCubicBound S (frequencyDyad j)*E/(1+c*2^j)^A := by
        apply (le_div_iff₀ (by positivity : 0 < (1+c*(2 : ℝ)^j)^A)).mpr
        simpa only [mul_comm,E] using hrec
      _ = _ := by ring
  have hs := summable_dualDyadicNorm S (fun a ha => (hS a ha).1) hc hA
  have hd := hasSum_coprimePoissonDyad S hS u W hW hW' hZ
  calc
    _ = ‖∑' j : ℕ, coprimePoissonDyad S (frequencyDyad j) u W Z‖ := by rw [hd.tsum_eq]
    _ ≤ ∑' j : ℕ, ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ :=
      norm_tsum_le_tsum_norm hd.summable.norm
    _ ≤ ∑' j : ℕ, (C*(Z/N)*E)*(finiteCubicBound S (frequencyDyad j)/(1+c*2^j)^A) :=
      Summable.tsum_le_tsum hterm hd.summable.norm (hs.mul_left _)
    _ = _ := by rw [tsum_mul_left]; dsimp [dualDyadicNorm,c,E]; ring

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

theorem primarySmoothedSieveMass_norm_recurrence (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A : ℕ) (hA : 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (u : Eisenstein → ℂ) (Z N : ℝ), 0 < Z → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ‖primarySmoothedSieveMass S u W Z‖ ≤ C *
        ∑ k ∈ commonRowFactors S,
          (∑ s ∈ (primaryPrimeFactors k).powerset,
            commonBlockCost S W Z N A k (∏ p ∈ s, p)) * commonBlockEnergy S u k := by
  obtain ⟨C₀,hC₀,hrec⟩ := coprimeGramForm_norm_recurrence W hW hW' A hA
  let C := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have h1C : 1 ≤ C := le_max_right _ _
  have hC₀C : C₀ ≤ C := le_max_left _ _
  refine ⟨C,hC,?_⟩
  intro S hS u Z N hZ hN hSN
  have hblock (k : Eisenstein) (hkS : k ∈ commonRowFactors S)
      (s : Finset Eisenstein) (hs : s ∈ (primaryPrimeFactors k).powerset) :
      let m := ∏ p ∈ s, p
      ‖(idealMoebius m : ℂ) * coprimeGramForm (residualRows S k)
        (commonBlockCoefficient u k m) W (Z/norm m)‖ ≤
        C * commonBlockCost S W Z N A k m * commonBlockEnergy S u k := by
    dsimp only
    let m := ∏ p ∈ s, p
    have hk := commonRowFactors_spec hS hkS
    have hm : primary m := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).1.1)
    have hmk : 0 < norm k := norm_pos_of_ne_zero (primary_ne_zero hk.1)
    have hmm : 0 < norm m := norm_pos_of_ne_zero (primary_ne_zero hm)
    have hre := residualRows_primary hk.1 hS
    have hbound : ‖coprimeGramForm (residualRows S k) (commonBlockCoefficient u k m) W (Z/norm m)‖ ≤
        C * commonBlockCost S W Z N A k m * commonBlockEnergy S u k := by
      by_cases hkN : norm k < N
      · have hd := dualDyadicNorm_nonneg (residualRows S k)
          (by positivity : 0 ≤ (Z/norm m)/(27*(N/norm k)^2)) A
        have hh := hrec (residualRows S k)
          (fun a ha => ⟨(hre a ha).1,(hre a ha).2,
            residualRows_nonunit hk.1 hkN (fun p hp => (hSN p hp).1) a ha⟩)
          (commonBlockCoefficient u k m) (Z/norm m) (N/norm k)
          (div_pos hZ hmm) (div_pos hN hmk) (residualRows_norm hk.1 hSN)
        rw [commonBlockCost,ite_eq_left hkN]
        calc
          _ ≤ C₀*((Z/norm m)/(N/norm k))*
              dualDyadicNorm (residualRows S k) ((Z/norm m)/(27*(N/norm k)^2)) A *
              commonBlockEnergy S u k := hh.trans (mul_le_mul_of_nonneg_left
                (commonBlockCoefficient_energy_le S hS u hk.1 m)
                (mul_nonneg (mul_nonneg hC₀.le (by positivity)) hd))
          _ = C₀ * (((Z/norm m)/(N/norm k))*
              dualDyadicNorm (residualRows S k) ((Z/norm m)/(27*(N/norm k)^2)) A) *
              commonBlockEnergy S u k := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC₀C (mul_nonneg (by positivity) hd))
            (commonBlockEnergy_nonneg S u k)
      · rw [commonBlockCost,ite_eq_right hkN]
        calc
          _ ≤ ‖primaryCharacterGram 1 1 W (Z/norm m)‖ *
              ∑ a ∈ residualRows S k, ‖commonBlockCoefficient u k m a‖^2 :=
            coprimeGramForm_subset_singleton _
              (residualRows_subset_one hk.1 (fun p hp => (hS p hp).1) (le_of_not_gt hkN)
                (fun p hp => (hSN p hp).2)) _ _ _
          _ ≤ ‖primaryCharacterGram 1 1 W (Z/norm m)‖ * commonBlockEnergy S u k :=
            mul_le_mul_of_nonneg_left (commonBlockCoefficient_unweighted_energy_le S hS u hk.1 m)
              (_root_.norm_nonneg _)
          _ ≤ _ := by
            have he : 0 ≤ ‖primaryCharacterGram 1 1 W (Z/norm m)‖ * commonBlockEnergy S u k :=
              mul_nonneg (_root_.norm_nonneg _) (commonBlockEnergy_nonneg S u k)
            nlinarith [mul_le_mul_of_nonneg_right h1C he]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one m)).trans hbound
  rw [primarySmoothedSieveMass_common_blocks S hS u W hW hW' hZ]
  calc
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        ‖(idealMoebius (∏ p ∈ s, p) : ℂ) * coprimeGramForm (residualRows S k)
          (commonBlockCoefficient u k (∏ p ∈ s, p)) W (Z/norm (∏ p ∈ s, p))‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => norm_sum_le _ _))
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        C * commonBlockCost S W Z N A k (∏ p ∈ s, p) * commonBlockEnergy S u k :=
      Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun s hs => hblock k hk s hs))
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

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
-- module Solutions.OAIQ096_CM.CubicGram_SieveExponent
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma squarefreePrimaryDyad_card_le (j : ℕ) :
    ((squarefreePrimaryDyad j).card : ℝ) ≤ 36*(2 : ℝ)^j := by
  exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (frequencyDyad_card_le j)

lemma cubeDyad_sizes {j : ℕ} {z : ℕ×ℕ×ℕ} (hz : z ∈ cubeDyadTriples j) :
    (2 : ℝ)^z.1*((2 : ℝ)^z.2.1)^2*((2 : ℝ)^z.2.2)^3 ≤ 2*(2 : ℝ)^j := by
  have hh := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (mem_cubeDyadTriples.mp hz))
  calc
    _ = (2 : ℝ)^(z.1+2*z.2.1+3*z.2.2) := by
      simp only [pow_add,pow_mul,mul_comm 2 z.2.1,mul_comm 3 z.2.2]
    _ ≤ 2^(j+1) := hh
    _ = _ := by rw [pow_succ]; ring

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_block_scaled {S T K N J ξ C : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (hK : 1 ≤ K) (hN : 0 ≤ N)
    (hJ : S*T^2*K^3 ≤ J) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) (hC : 0 ≤ C) :
    min (T*K*(C*(N+(N*S)^(2/3 : ℝ)+S^ξ)))
      (S*K*(C*(N+(N*T)^(2/3 : ℝ)+T^ξ))) ≤
      C*(N*J^(1/3 : ℝ)+(J*N)^(2/3 : ℝ)+J^ξ+J) := by
  have he (a b : ℝ) : a*K*(C*b) = C*(K*a*b) := by ring
  simp only [he,← mul_min_of_nonneg _ _ hC]
  exact mul_le_mul_of_nonneg_left (cube_block_numerical hS hT hK hN hJ hξ hξ2) hC

lemma cube_scaled_sizes {j : ℕ} {z : ℕ×ℕ×ℕ} (hz : z ∈ cubeDyadTriples j) :
    (2*(2 : ℝ)^z.1)*(2*(2 : ℝ)^z.2.1)^2*(2*(2 : ℝ)^z.2.2)^3 ≤ 128*(2 : ℝ)^j := by
  have h := mul_le_mul_of_nonneg_left (cubeDyad_sizes hz) (by norm_num : (0 : ℝ) ≤ 64)
  nlinarith only [h]

lemma SieveExponent.cube_bound {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      ∀ j : ℕ,
      finiteCubicBound P (frequencyDyad j) ≤ D*(N*(128*(2 : ℝ)^j))^ε*
        (N*(128*(2 : ℝ)^j)^(1/3 : ℝ)+(128*(2 : ℝ)^j*N)^(2/3 : ℝ)+
         (128*(2 : ℝ)^j)^ξ+128*(2 : ℝ)^j) := by
  obtain ⟨C,hC,hbound⟩ := hExp (ε/2) (by linarith)
  obtain ⟨E,hE,hpoly⟩ := dyadic_polynomial_small_power 3 (show 0 < ε/2 by linarith)
  refine ⟨((nonzeroNormBall 729).card+1)*324*C*E,by positivity,?_⟩
  intro P N hN hP j
  let J : ℝ := 128*(2 : ℝ)^j
  let F : ℝ := N*J^(1/3 : ℝ)+(J*N)^(2/3 : ℝ)+J^ξ+J
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hJ : 1 ≤ J := by dsimp [J]; have : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num); linarith
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpp := fun b hb => (hP b hb).1
  have hsf (i : ℕ) : ∀ a ∈ squarefreePrimaryDyad i, primary a ∧ Squarefree a ∧ norm a ≤ 2*(2 : ℝ)^i := by
    intro a ha
    have hh := mem_squarefreePrimaryDyad.mp ha
    exact ⟨hh.2.1,hh.2.2,(frequencyDyad_norm hh.1).2⟩
  have hn (i : ℕ) : 1 ≤ 2*(2 : ℝ)^i := by have : (1 : ℝ) ≤ 2^i := one_le_pow₀ (by norm_num); linarith
  have hsieve (i : ℕ) (hi : 2*(2 : ℝ)^i ≤ J) :
      finiteCubicBound P (squarefreePrimaryDyad i) ≤ C*(N*J)^(ε/2)*
        (N+(N*(2*(2 : ℝ)^i))^(2/3 : ℝ)+(2*(2 : ℝ)^i)^ξ) := by
    rw [finiteCubicBound_symm P _ hpp (fun a ha => (hsf i a ha).1)]
    apply (hbound _ _ N (2*(2 : ℝ)^i) hN (hn i) (hsf i) hP).trans
    gcongr
  have hblock (z : ℕ×ℕ×ℕ) (hz : z ∈ cubeDyadTriples j) :
      min (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card*
        finiteCubicBound P (squarefreePrimaryDyad z.1))
        (((squarefreePrimaryDyad z.1).card : ℝ)*(frequencyDyad z.2.2).card*
        finiteCubicBound P (squarefreePrimaryDyad z.2.1)) ≤
          324*C*(N*J)^(ε/2)*F := by
    let S : ℝ := 2*(2 : ℝ)^z.1
    let T : ℝ := 2*(2 : ℝ)^z.2.1
    let K : ℝ := 2*(2 : ℝ)^z.2.2
    have hS : 1 ≤ S := hn _
    have hT : 1 ≤ T := hn _
    have hK : 1 ≤ K := hn _
    have hprod : S*T^2*K^3 ≤ J := cube_scaled_sizes hz
    have hSle : S ≤ J := (le_mul_of_one_le_right (by linarith : 0 ≤ S)
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) (one_le_pow₀ hK))).trans
      (by simpa only [mul_assoc] using hprod)
    have hTle : T ≤ J := by
      have ht : T ≤ T^2 := le_self_pow₀ hT (by norm_num : (2 : ℕ) ≠ 0)
      have ht' : T^2 ≤ S*T^2*K^3 := by
        calc
          _ ≤ S*T^2 := le_mul_of_one_le_left (sq_nonneg _) hS
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hK)
      exact ht.trans (ht'.trans hprod)
    have hcardS : ((squarefreePrimaryDyad z.1).card : ℝ) ≤ 18*S := by dsimp [S]; nlinarith [squarefreePrimaryDyad_card_le z.1]
    have hcardT : ((squarefreePrimaryDyad z.2.1).card : ℝ) ≤ 18*T := by dsimp [T]; nlinarith [squarefreePrimaryDyad_card_le z.2.1]
    have hcardK : ((frequencyDyad z.2.2).card : ℝ) ≤ 18*K := by dsimp [K]; nlinarith [frequencyDyad_card_le z.2.2]
    calc
      _ ≤ min ((18*T)*(18*K)*(C*(N*J)^(ε/2)*(N+(N*S)^(2/3 : ℝ)+S^ξ)))
          ((18*S)*(18*K)*(C*(N*J)^(ε/2)*(N+(N*T)^(2/3 : ℝ)+T^ξ))) := by
        have hbs := hsieve _ hSle
        have hbt := hsieve _ hTle
        have hbs0 := finiteCubicBound_nonneg P (squarefreePrimaryDyad z.1)
        have hbt0 := finiteCubicBound_nonneg P (squarefreePrimaryDyad z.2.1)
        apply min_le_min <;> gcongr
      _ = min (T*K*((324*C*(N*J)^(ε/2))*(N+(N*S)^(2/3 : ℝ)+S^ξ)))
          (S*K*((324*C*(N*J)^(ε/2))*(N+(N*T)^(2/3 : ℝ)+T^ξ))) := by congr 1 <;> ring
      _ ≤ _ := cube_block_scaled hS hT hK hN0.le hprod hξ hξ2 (by positivity)
  have hcount : ((cubeDyadTriples j).card : ℝ) ≤ E*J^(ε/2) := by
    have hc : ((cubeDyadTriples j).card : ℝ) ≤ ((j : ℝ)+2)^3 := by exact_mod_cast cubeDyadTriples_card j
    apply (hc.trans (hpoly j)).trans
    gcongr
    dsimp [J]
    have hh : (0 : ℝ) ≤ 2^j := by positivity
    linarith
  have hpow : J^(ε/2)*(N*J)^(ε/2) ≤ (N*J)^ε := by
    calc
      _ ≤ (N*J)^(ε/2)*(N*J)^(ε/2) := by
        gcongr
        exact le_mul_of_one_le_left hJ0.le hN
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  calc
    _ ≤ (nonzeroNormBall 729).card*∑ z ∈ cubeDyadTriples j,
        min (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card*
          finiteCubicBound P (squarefreePrimaryDyad z.1))
          (((squarefreePrimaryDyad z.1).card : ℝ)*(frequencyDyad z.2.2).card*
          finiteCubicBound P (squarefreePrimaryDyad z.2.1)) := finiteCubicBound_frequency_cube P hpp j
    _ ≤ (nonzeroNormBall 729).card*(((cubeDyadTriples j).card : ℝ)*(324*C*(N*J)^(ε/2)*F)) :=
      mul_le_mul_of_nonneg_left ((Finset.sum_le_card_nsmul _ _ _ hblock).trans_eq (by rw [nsmul_eq_mul])) (by positivity)
    _ ≤ (nonzeroNormBall 729).card*(E*J^(ε/2)*(324*C*(N*J)^(ε/2)*F)) := by gcongr
    _ = ((nonzeroNormBall 729).card*324*C*E)*(J^(ε/2)*(N*J)^(ε/2))*F := by ring
    _ ≤ ((nonzeroNormBall 729).card*324*C*E)*(N*J)^ε*F := by gcongr
    _ ≤ _ := by dsimp only [F,J]; gcongr; linarith

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma decayConstant_pos {α : ℝ} (hα : 0 < α) : 0 < decayConstant α := by
  have hp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hα
  dsimp [decayConstant]; positivity

lemma finite_polynomial_dyadic_bound {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (ha : ∀ i, 0 < a i ∧ a i ≤ 4) (hv : ∀ i, 0 ≤ v i)
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hb : ∀ j, f j ≤ ∑ i, v i*((2 : ℝ)^j)^(a i))
    {c : ℝ} (hc : 0 < c) :
    (∑' j : ℕ, f j/(1+c*2^j)^8) ≤ ∑ i, v i*decayConstant (a i)*c^(-(a i)) := by
  have hs (i : ι) := (real_dyadic_decay (a i) (ha i).1 (ha i).2 hc).1.mul_left (v i)
  have hsum : Summable (fun j : ℕ => ∑ i, v i*(((2 : ℝ)^j)^(a i)/(1+c*2^j)^8)) :=
    summable_sum (fun i _ => hs i)
  have hmajor (j : ℕ) : f j/(1+c*2^j)^8 ≤ ∑ i, v i*(((2 : ℝ)^j)^(a i)/(1+c*2^j)^8) := by
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hb j) (by positivity)
  have hf' := hsum.of_nonneg_of_le (fun j => div_nonneg (hf j) (by positivity)) hmajor
  calc
    _ ≤ ∑' j : ℕ, ∑ i, v i*(((2 : ℝ)^j)^(a i)/(1+c*2^j)^8) := hf'.tsum_le_tsum hmajor hsum
    _ = ∑ i, v i*∑' j : ℕ, ((2 : ℝ)^j)^(a i)/(1+c*2^j)^8 := by
      rw [Summable.tsum_finsetSum (fun i _ => hs i)]
      simp only [tsum_mul_left]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => (mul_le_mul_of_nonneg_left
      (real_dyadic_decay (a i) (ha i).1 (ha i).2 hc).2 (hv i)).trans_eq (by dsimp [decayConstant]; ring))

lemma SieveExponent.dual_bound {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N c : ℝ), 1 ≤ N → 0 < c →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      dualDyadicNorm P c 8 ≤ C*N^δ*
        (N*c^(-(δ+1/3 : ℝ))+N^(2/3 : ℝ)*c^(-(δ+2/3 : ℝ))+
          c^(-(δ+ξ))+c^(-(δ+1))) := by
  obtain ⟨D,hD,hcube⟩ := hExp.cube_bound hξ hξ2 hδ
  let a : Fin 4 → ℝ := ![δ+1/3,δ+2/3,δ+ξ,δ+1]
  have ha : ∀ i, 0 < a i ∧ a i ≤ 4 := by intro i; fin_cases i <;> dsimp [a] <;> constructor <;> linarith
  let E : ℝ := ∑ i : Fin 4, (128 : ℝ)^(a i)*decayConstant (a i)
  have htermpos (i : Fin 4) : 0 < (128 : ℝ)^(a i)*decayConstant (a i) :=
    mul_pos (by positivity) (decayConstant_pos (ha i).1)
  have hE : 0 < E := by
    exact Finset.sum_pos (fun i _ => htermpos i) (Finset.univ_nonempty)
  refine ⟨D*E,by positivity,?_⟩
  intro P N c hN hc hP
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  let w : Fin 4 → ℝ := ![N,N^(2/3 : ℝ),1,1]
  have hw : ∀ i, 0 ≤ w i := by intro i; fin_cases i <;> dsimp [w] <;> positivity
  let v : Fin 4 → ℝ := fun i => D*N^δ*w i*(128 : ℝ)^(a i)
  have hv : ∀ i, 0 ≤ v i := by intro i; dsimp [v]; exact mul_nonneg (mul_nonneg (by positivity) (hw i)) (by positivity)
  have hexpand (j : ℕ) : D*(N*(128*(2 : ℝ)^j))^δ*
        (N*(128*(2 : ℝ)^j)^(1/3 : ℝ)+(128*(2 : ℝ)^j*N)^(2/3 : ℝ)+
         (128*(2 : ℝ)^j)^ξ+128*(2 : ℝ)^j) =
      ∑ i : Fin 4, v i*((2 : ℝ)^j)^(a i) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,Matrix.cons_val_zero,
      Matrix.cons_val_succ,v,w,a,add_zero]
    simp only [Real.mul_rpow (by positivity : (0 : ℝ) ≤ N) (by positivity : (0 : ℝ) ≤ 128*(2 : ℝ)^j),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) (by positivity : (0 : ℝ) ≤ (2 : ℝ)^j),
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 128*(2 : ℝ)^j) (by positivity : (0 : ℝ) ≤ N),
      Real.rpow_add (by norm_num : (0 : ℝ) < 128),Real.rpow_add (by positivity : (0 : ℝ) < (2 : ℝ)^j),Real.rpow_one]
    ring
  have hh := finite_polynomial_dyadic_bound a v ha hv (fun j => finiteCubicBound P (frequencyDyad j))
    (fun j => finiteCubicBound_nonneg _ _)
    (fun j => (hcube P N hN hP j).trans_eq (hexpand j)) hc
  have hEi (i : Fin 4) : (128 : ℝ)^(a i)*decayConstant (a i) ≤ E :=
    Finset.single_le_sum (fun i _ => (htermpos i).le) (Finset.mem_univ i)
  calc
    _ ≤ ∑ i : Fin 4, v i*decayConstant (a i)*c^(-(a i)) := hh
    _ = ∑ i : Fin 4, (D*N^δ)*(w i*c^(-(a i)))*((128 : ℝ)^(a i)*decayConstant (a i)) := by
      apply Finset.sum_congr rfl; intro i _; dsimp [v]; ring
    _ ≤ ∑ i : Fin 4, (D*N^δ)*(w i*c^(-(a i)))*E := by
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (hEi i) (mul_nonneg (by positivity) (mul_nonneg (hw i) (by positivity)))
    _ = _ := by
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,a,w,Matrix.cons_val_zero,
        Matrix.cons_val_succ,add_zero,one_mul]
      ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PoissonBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson numerical estimates and local-to-global sieve bounds. -/

section

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma poisson_power_identity {z n : ℝ} (hz : 0 < z) (hn : 0 < n) (r : ℝ) :
    (z/n)*(27*n^2/z)^r = 27^r*z^(1-r)*n^(2*r-1) := by
  rw [Real.div_rpow (by positivity) hz.le,Real.mul_rpow (by norm_num) (by positivity),
    Real.rpow_sub hz,Real.rpow_one,Real.rpow_sub hn,Real.rpow_one,
    Real.rpow_mul hn.le]
  norm_num only [Real.rpow_two]
  ring

lemma dual_length_neg_power {z n : ℝ} (hz : 0 < z) (hn : 0 < n) (r : ℝ) :
    (z/(27*n^2))^(-r) = (27*n^2/z)^r := by
  rw [Real.rpow_neg (by positivity),← Real.inv_rpow (by positivity)]
  congr 1
  field_simp

lemma poisson_cross_one {z n : ℝ} (hz : 0 < z) (hn : 0 < n) :
    (z/n)*(2*n)*(27*n^2/z)^(1/3 : ℝ) ≤ 6*(z*n)^(2/3 : ℝ) := by
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (z/n)*(2*n)*(27*n^2/z)^(1/3 : ℝ))
    (by positivity : 0 ≤ 6*(z*n)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
  simp only [mul_pow]
  rw [rpow_third_cube (by positivity),rpow_two_thirds_cube (by positivity)]
  field_simp
  nlinarith

lemma poisson_cross_two {z n : ℝ} (hz : 0 < z) (hn : 0 < n) (hnz : n ≤ z) :
    (z/n)*(2*n)^(2/3 : ℝ)*(27*n^2/z)^(2/3 : ℝ) ≤ 54*(z*n)^(2/3 : ℝ) := by
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (z/n)*(2*n)^(2/3 : ℝ)*(27*n^2/z)^(2/3 : ℝ))
    (by positivity : 0 ≤ 54*(z*n)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
  simp only [mul_pow]
  rw [rpow_two_thirds_cube (by positivity),rpow_two_thirds_cube (by positivity),
    rpow_two_thirds_cube (by positivity)]
  have hne := mul_le_mul_of_nonneg_left hnz (by positivity : 0 ≤ z*n^2)
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hnz (by positivity : 0 ≤ z*n^2)]

lemma poisson_dual_numerical {ξ δ z n : ℝ} (_hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n) (hnz : n ≤ z) :
    (z/n)*(2*n)^δ*
      ((2*n)*(z/(27*n^2))^(-(δ+1/3 : ℝ))+
       (2*n)^(2/3 : ℝ)*(z/(27*n^2))^(-(δ+2/3 : ℝ))+
       (z/(27*n^2))^(-(δ+ξ))+(z/(27*n^2))^(-(δ+1))) ≤
       (54000 : ℝ)*(z*n)^δ*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1)) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hz : 0 < z := hn0.trans_le hnz
  let t : ℝ := 27*n^2/z
  have ht : 0 < t := by dsimp [t]; positivity
  have heps : (2*n*t)^δ ≤ 54*(z*n)^δ := by
    have hlen : 2*n*t ≤ 54*(z*n) := by
      dsimp [t]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hz).mpr
      nlinarith [sq_le_sq₀ hn0.le hz.le |>.mpr hnz]
    calc
      _ ≤ (54*(z*n))^δ := Real.rpow_le_rpow (by positivity) hlen hδ.le
      _ = 54^δ*(z*n)^δ := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 54*(z*n)^δ := by
        have hh : (54 : ℝ)^δ ≤ 54 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 54) hδ1
        gcongr
  have h1 : (z/n)*((2*n)*t^(1/3 : ℝ)) ≤ 6*(z*n)^(2/3 : ℝ) := by
    simpa only [← mul_assoc] using poisson_cross_one hz hn0
  have h2 : (z/n)*((2*n)^(2/3 : ℝ)*t^(2/3 : ℝ)) ≤ 54*(z*n)^(2/3 : ℝ) := by
    simpa only [← mul_assoc] using poisson_cross_two hz hn0 hnz
  have hx : (z/n)*t^ξ ≤ 729*(z^(1-ξ)*n^(2*ξ-1)) := by
    rw [poisson_power_identity hz hn0]
    have hp : (27 : ℝ)^ξ ≤ 729 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 27) hξ2
      norm_num at hh ⊢
      exact hh
    calc
      _ = 27^ξ*(z^(1-ξ)*n^(2*ξ-1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  have hlast : (z/n)*t = 27*n := by dsimp [t]; field_simp
  have hsum : (z/n)*((2*n)*t^(1/3 : ℝ)+(2*n)^(2/3 : ℝ)*t^(2/3 : ℝ)+t^ξ+t) ≤
      1000*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1)) := by
    have hnon : 0 ≤ (z*n)^(2/3 : ℝ) := by positivity
    have hnon' : 0 ≤ z^(1-ξ)*n^(2*ξ-1) := by positivity
    nlinarith
  have hexpand : (z/n)*(2*n)^δ*
      ((2*n)*(z/(27*n^2))^(-(δ+1/3 : ℝ))+
       (2*n)^(2/3 : ℝ)*(z/(27*n^2))^(-(δ+2/3 : ℝ))+
       (z/(27*n^2))^(-(δ+ξ))+(z/(27*n^2))^(-(δ+1))) =
      (2*n*t)^δ*((z/n)*((2*n)*t^(1/3 : ℝ)+(2*n)^(2/3 : ℝ)*t^(2/3 : ℝ)+t^ξ+t)) := by
    simp only [dual_length_neg_power hz hn0,
      Real.mul_rpow (by positivity : 0 ≤ 2*n) ht.le]
    dsimp only [t]
    rw [Real.rpow_add (by positivity),Real.rpow_add (by positivity),Real.rpow_add (by positivity),Real.rpow_add (by positivity),Real.rpow_one]
    ring
  rw [hexpand]
  calc
    _ ≤ (54*(z*n)^δ)*(1000*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1))) :=
      mul_le_mul heps hsum (by positivity) (by positivity)
    _ = _ := by ring

end CubicFirstMoment
end
end

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

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finiteCubicBound_empty (H : Finset Eisenstein) : finiteCubicBound ∅ H = 0 := by
  apply le_antisymm _ (finiteCubicBound_nonneg _ _)
  apply (finiteCubicBound_le_iff _ _ (by norm_num : (0 : ℝ) ≤ 0)).mpr
  intro u
  simp

lemma finiteCubicBound_local_to_global (S H : Finset Eisenstein) (N F : ℝ)
    (hN : 1 ≤ N) (hF : 0 ≤ F)
    (hS : ∀ a ∈ S, primary a ∧ norm a ≤ N) (hH : ∀ x ∈ H, primary x)
    (hlocal : ∀ (R : Finset Eisenstein), R ⊆ S → ∀ n : ℝ, 1 ≤ n → n ≤ N →
      (∀ a ∈ R, n ≤ norm a ∧ norm a ≤ Real.sqrt 2*n) → finiteCubicBound R H ≤ F) :
      finiteCubicBound S H ≤ 2*((Nat.log 2 ⌊N⌋₊ : ℝ)+1)*F := by
  let L := Nat.log 2 ⌊N⌋₊
  let R : ℕ → Finset Eisenstein := fun j => S.filter (fun a => Nat.log 2 (normNat a) = j)
  have hN0 : 0 < N := zero_lt_one.trans_le hN
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
    have hn : normNat a ≤ ⌊N⌋₊ := Nat.le_floor (by rw [normNat_cast]; exact (hS a ha).2)
    have hl : Nat.log 2 (normNat a) ≤ L := Nat.log_mono_right hn
    omega
  have hR (j : ℕ) : ∀ a ∈ R j, (2 : ℝ)^j ≤ norm a ∧ norm a ≤ 2*(2 : ℝ)^j := by
    intro a ha
    have hh := Finset.mem_filter.mp ha
    exact frequencyDyad_norm (mem_frequencyDyad.mpr ⟨primary_ne_zero (hS a hh.1).1,hh.2⟩)
  have hterm (j : ℕ) (hj : j ∈ Finset.range (L+1)) : finiteCubicBound H (R j) ≤ 2*F := by
    have hjL : j ≤ L := by have := Finset.mem_range.mp hj; omega
    have hpowj : (2 : ℝ)^j ≤ N := (pow_le_pow_right₀ (by norm_num) hjL).trans hpow
    have hprim : ∀ a ∈ R j, primary a := fun a ha => (hS a (Finset.mem_filter.mp ha).1).1
    rw [finiteCubicBound_symm H _ hH hprim]
    let A := (R j).filter (fun a => norm a ≤ Real.sqrt 2*(2 : ℝ)^j)
    let B := (R j).filter (fun a => ¬norm a ≤ Real.sqrt 2*(2 : ℝ)^j)
    have hAS : A ⊆ S := fun a ha => (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
    have hBS : B ⊆ S := fun a ha => (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
    have hA : finiteCubicBound A H ≤ F := hlocal A hAS ((2 : ℝ)^j)
      (one_le_pow₀ (by norm_num)) hpowj (fun a ha =>
        ⟨(hR j a (Finset.mem_filter.mp ha).1).1,(Finset.mem_filter.mp ha).2⟩)
    have hB : finiteCubicBound B H ≤ F := by
      by_cases hBN : Real.sqrt 2*(2 : ℝ)^j ≤ N
      · refine hlocal B hBS (Real.sqrt 2*(2 : ℝ)^j) ?_ hBN ?_
        · exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num))
        · intro a ha
          have hh := Finset.mem_filter.mp ha
          refine ⟨le_of_not_ge hh.2,?_⟩
          rw [← mul_assoc,Real.mul_self_sqrt (by norm_num)]
          exact (hR j a hh.1).2
      · have he : B = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a ha
          have hlo := (Finset.mem_filter.mp ha).2
          have hhi := (hS a (hBS ha)).2
          exact hlo (hhi.trans (le_of_not_ge hBN))
        rw [he,finiteCubicBound_empty]
        exact hF
    have hh := finiteCubicBound_split (R j) H (fun a => norm a ≤ Real.sqrt 2*(2 : ℝ)^j) hprim hH
    change finiteCubicBound (R j) H ≤ finiteCubicBound A H+finiteCubicBound B H at hh
    linarith
  calc
    _ = finiteCubicBound H S := finiteCubicBound_symm S H (fun a ha => (hS a ha).1) hH
    _ ≤ finiteCubicBound H ((Finset.range (L+1)).biUnion R) := finiteCubicBound_mono (Finset.Subset.refl H) hcover
    _ ≤ ∑ j ∈ Finset.range (L+1), finiteCubicBound H (R j) := finiteCubicBound_biUnion _ _ _
    _ ≤ (L+1 : ℝ)*(2*F) := by
      have hh := Finset.sum_le_card_nsmul _ _ _ hterm
      simpa only [Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using hh
    _ = _ := by ring

lemma cutoff_log_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → (Nat.log 2 ⌊N⌋₊ : ℝ)+1 ≤ C*N^ε := by
  obtain ⟨C,hC,h⟩ := dyadic_polynomial_small_power 1 hε
  refine ⟨C,hC,?_⟩
  intro N hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hfloor : ⌊N⌋₊ ≠ 0 := by
    have hh : (1 : ℕ) ≤ ⌊N⌋₊ := by apply Nat.le_floor; simpa using hN
    omega
  have hpow : (2 : ℝ)^(Nat.log 2 ⌊N⌋₊) ≤ N := by
    have hr : (2 : ℝ)^(Nat.log 2 ⌊N⌋₊) ≤ (⌊N⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hfloor
    exact hr.trans (Nat.floor_le hN0.le)
  have hh := h (Nat.log 2 ⌊N⌋₊)
  simp only [pow_one] at hh
  have hp : C*((2 : ℝ)^(Nat.log 2 ⌊N⌋₊))^ε ≤ C*N^ε := by gcongr
  linarith

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_QuantitativeRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma scaled_poisson_error_le {ξ M N m k : ℝ} (hξ : 1 ≤ ξ)
    (hM : 0 < M) (hN : 0 < N) (hm : 1 ≤ m) (hk : m ≤ k) :
    (M/m)^(1-ξ)*(N/k)^(2*ξ-1) ≤ M^(1-ξ)*N^(2*ξ-1) := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hk0 : 0 < k := hm0.trans_le hk
  have hk1 : 1 ≤ k := hm.trans hk
  have hp : m^(ξ-1) ≤ k^(2*ξ-1) := by
    calc
      _ ≤ k^(ξ-1) := Real.rpow_le_rpow hm0.le hk (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  have hden : 1 ≤ m^(1-ξ)*k^(2*ξ-1) := by
    rw [show (1 : ℝ)-ξ = -(ξ-1) by ring,Real.rpow_neg hm0.le]
    rw [inv_mul_eq_div]
    exact (one_le_div (by positivity)).mpr hp
  rw [Real.div_rpow hM.le hm0.le,Real.div_rpow hN.le hk0.le,← mul_div_mul_comm]
  exact div_le_self (by positivity) hden

lemma SieveExponent.common_cost_bound {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (M N : ℝ), 1 ≤ N → N ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ∀ k ∈ commonRowFactors S, ∀ s ∈ (primaryPrimeFactors k).powerset,
      commonBlockCost S cubicSieveCutoff M N 8 k (∏ p ∈ s, p) ≤
        C*(M*N)^δ*sieveRecurrenceShape ξ M N := by
  obtain ⟨D,hD,hdual⟩ := hExp.dual_bound hξ hξ2 hδ hδ1
  obtain ⟨E,hE,hdiag⟩ := primaryCharacterGram_one_one_bound cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth.continuous
  let C : ℝ := 54000*D+E
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : 54000*D ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro S M N hN hNM hS k hkS s hs
  let m := ∏ p ∈ s, p
  have hS' : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hk := commonRowFactors_spec hS' hkS
  have hm : primary m := primary_finset_prod _ _
    (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).1.1)
  have hmk : m ∣ k := (primary_subsets_prod_dvd hk.1 (Finset.mem_powerset.mp hs) k).mpr
    (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).2)
  have hnk1 : 1 ≤ norm k := one_le_norm (primary_ne_zero hk.1)
  have hnm1 : 1 ≤ norm m := one_le_norm (primary_ne_zero hm)
  have hnk : 0 < norm k := zero_lt_one.trans_le hnk1
  have hnm : 0 < norm m := zero_lt_one.trans_le hnm1
  have hmkN : norm m ≤ norm k := norm_le_of_dvd (primary_ne_zero hk.1) hmk
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := hN0.trans_le hNM
  have hM1 : 1 ≤ M := hN.trans hNM
  have hMN1 : 1 ≤ M*N := one_le_mul_of_one_le_of_one_le hM1 hN
  have hpow1 : 1 ≤ (M*N)^δ := Real.one_le_rpow hMN1 hδ.le
  have hshape := sieveRecurrenceShape_nonneg (ξ := ξ) hM0.le hN0.le
  have hMshape : M ≤ sieveRecurrenceShape ξ M N := by
    unfold sieveRecurrenceShape
    have hh : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
    have hh' : 0 ≤ M^(1-ξ)*N^(2*ξ-1) := by positivity
    linarith
  change commonBlockCost S cubicSieveCutoff M N 8 k m ≤ _
  unfold commonBlockCost
  split_ifs with hkN
  · let n : ℝ := N/norm k
    let z : ℝ := M/norm m
    have hn : 1 ≤ n := by dsimp [n]; exact (one_le_div hnk).mpr hkN.le
    have hn0 : 0 < n := zero_lt_one.trans_le hn
    have hnz : n ≤ z := by
      dsimp [n,z]
      apply (div_le_div_iff₀ hnk hnm).mpr
      nlinarith [mul_le_mul hNM hmkN (norm_nonneg m) hM0.le]
    have hz : 0 < z := hn0.trans_le hnz
    have hnN : n ≤ N := div_le_self hN0.le hnk1
    have hzM : z ≤ M := div_le_self hM0.le hnm1
    have hzn : z*n ≤ M*N := mul_le_mul hzM hnN hn0.le hM0.le
    have hres : ∀ a ∈ residualRows S k, primary a ∧ Squarefree a ∧ norm a ≤ 2*n := by
      intro a ha
      have hh := residualRows_primary hk.1 hS' a ha
      refine ⟨hh.1,hh.2,?_⟩
      have hnorm := (residualRows_norm hk.1 (fun p hp => (hS p hp).2.2) a ha).2
      have hsqrt : Real.sqrt 2 ≤ 2 := by norm_num
      exact hnorm.trans (mul_le_mul_of_nonneg_right hsqrt hn0.le)
    have hbound := hdual (residualRows S k) (2*n) (z/(27*n^2)) (by linarith) (by positivity) hres
    have hnum := poisson_dual_numerical hξ hξ2 hδ hδ1 hn hnz
    have herr : z^(1-ξ)*n^(2*ξ-1) ≤ M^(1-ξ)*N^(2*ξ-1) :=
      scaled_poisson_error_le hξ hM0 hN0 hnm1 hmkN
    have hbracket : (z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1) ≤ sieveRecurrenceShape ξ M N := by
      have hh : (z*n)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := Real.rpow_le_rpow (by positivity) hzn (by norm_num)
      unfold sieveRecurrenceShape
      linarith
    calc
      _ ≤ (z/n)*(D*(2*n)^δ*
        ((2*n)*(z/(27*n^2))^(-(δ+1/3 : ℝ))+(2*n)^(2/3 : ℝ)*(z/(27*n^2))^(-(δ+2/3 : ℝ))+
        (z/(27*n^2))^(-(δ+ξ))+(z/(27*n^2))^(-(δ+1)))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = D*((z/n)*(2*n)^δ*
        ((2*n)*(z/(27*n^2))^(-(δ+1/3 : ℝ))+(2*n)^(2/3 : ℝ)*(z/(27*n^2))^(-(δ+2/3 : ℝ))+
        (z/(27*n^2))^(-(δ+ξ))+(z/(27*n^2))^(-(δ+1)))) := by ring
      _ ≤ D*(54000*(z*n)^δ*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1))) :=
        mul_le_mul_of_nonneg_left hnum hD.le
      _ = (54000*D)*(z*n)^δ*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1)) := by ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ E*(M/norm m) := hdiag _ (div_pos hM0 hnm)
      _ ≤ C*M := mul_le_mul hEC (div_le_self hM0.le hnm1) (by positivity) hC.le
      _ ≤ C*((M*N)^δ*sieveRecurrenceShape ξ M N) := mul_le_mul_of_nonneg_left
        (hMshape.trans (le_mul_of_one_le_left hshape hpow1)) hC.le
      _ = _ := by ring

lemma SieveExponent.thin_recurrence {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ N → N ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N := by
  obtain ⟨C₀,hC₀,hrec⟩ := primarySmoothedSieveMass_norm_recurrence cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth 8 (by norm_num)
  obtain ⟨D,hD,hcost⟩ := hExp.common_cost_bound hξ hξ2 hδ hδ1
  obtain ⟨E,hE,henergy⟩ := common_energy_small_power δ hδ
  refine ⟨C₀*D*E*(Real.sqrt 2)^δ,by positivity,?_⟩
  intro S H M N hN hNM hS hH
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := hN0.trans_le hNM
  have hM1 : 1 ≤ M := hN.trans hNM
  have hS' : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hshape := sieveRecurrenceShape_nonneg (ξ := ξ) hM0.le hN0.le
  have hpow : (M*N)^δ*N^δ ≤ (M*N)^(2*δ) := by
    rw [show 2*δ = δ+δ by ring,Real.rpow_add (by positivity)]
    gcongr
    exact le_mul_of_one_le_left hN0.le hM1
  apply (finiteCubicBound_le_iff _ _ (by positivity)).mpr
  intro u
  have hb := hrec S hS' u M N hM0 hN0 (fun a ha => (hS a ha).2.2)
  have hsum : (∑ k ∈ commonRowFactors S,
       (∑ s ∈ (primaryPrimeFactors k).powerset,
         commonBlockCost S cubicSieveCutoff M N 8 k (∏ p ∈ s, p))*commonBlockEnergy S u k) ≤
      (D*(M*N)^δ*sieveRecurrenceShape ξ M N)*
        ∑ k ∈ commonRowFactors S, (2 : ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S u k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro k hk
    have hh := Finset.sum_le_card_nsmul _ _ _ (hcost S M N hN hNM hS k hk)
    simp only [Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
    exact (mul_le_mul_of_nonneg_right hh (commonBlockEnergy_nonneg _ _ _)).trans_eq (by ring)
  have he := henergy S u (Real.sqrt 2*N)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)
  calc
    _ ≤ ‖primarySmoothedSieveMass S u cubicSieveCutoff M‖ :=
      finiteCubicMass_le_smoothed S H (fun x hx => (hH x hx).1) u hM0 (fun x hx => (hH x hx).2)
    _ ≤ C₀*((D*(M*N)^δ*sieveRecurrenceShape ξ M N)*(E*(Real.sqrt 2*N)^δ*∑ a ∈ S, ‖u a‖^2)) :=
      hb.trans (mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left he (by positivity))) hC₀.le)
    _ = (C₀*D*E*(Real.sqrt 2)^δ)*((M*N)^δ*N^δ)*sieveRecurrenceShape ξ M N*∑ a ∈ S, ‖u a‖^2 := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) hN0.le]; ring
    _ ≤ _ := by gcongr

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sieveRecurrenceShape_mono_right {ξ M n N : ℝ} (hξ : 1 ≤ ξ)
    (hM : 0 ≤ M) (hn : 0 ≤ n) (hnN : n ≤ N) :
    sieveRecurrenceShape ξ M n ≤ sieveRecurrenceShape ξ M N := by
  unfold sieveRecurrenceShape
  gcongr
  linarith

lemma SieveExponent.recurrence_oai {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ N → N ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^ε*sieveRecurrenceShape ξ M N := by
  let δ : ℝ := min (ε/3) (1/3)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδε : 3*δ ≤ ε := by have := min_le_left (ε/3) (1/3 : ℝ); change δ ≤ ε/3 at this; linarith
  obtain ⟨D,hD,hthin⟩ := hExp.thin_recurrence hξ hξ2 hδ hδ1
  obtain ⟨E,hE,hlog⟩ := cutoff_log_small_power hδ
  refine ⟨2*E*D,by positivity,?_⟩
  intro S H M N hN hNM hS hH
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := hN0.trans_le hNM
  have hM1 : 1 ≤ M := hN.trans hNM
  have hshape := sieveRecurrenceShape_nonneg (ξ := ξ) hM0.le hN0.le
  have hlocal : ∀ R : Finset Eisenstein, R ⊆ S → ∀ n : ℝ, 1 ≤ n → n ≤ N →
      (∀ a ∈ R, n ≤ norm a ∧ norm a ≤ Real.sqrt 2*n) →
      finiteCubicBound R H ≤ D*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N := by
    intro R hRS n hn hnN hR
    have hh := hthin R H M n hn (hnN.trans hNM)
      (fun a ha => ⟨(hS a (hRS ha)).1,(hS a (hRS ha)).2.1,hR a ha⟩) hH
    have hs := sieveRecurrenceShape_mono_right hξ hM0.le (zero_lt_one.trans_le hn).le hnN
    exact hh.trans (mul_le_mul (by gcongr) hs (sieveRecurrenceShape_nonneg hM0.le (by linarith)) (by positivity))
  have hb := finiteCubicBound_local_to_global S H N
    (D*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N) hN (by positivity)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩) (fun x hx => (hH x hx).1) hlocal
  have hp : N^δ*(M*N)^(2*δ) ≤ (M*N)^ε := by
    calc
      _ ≤ (M*N)^δ*(M*N)^(2*δ) := by gcongr; exact le_mul_of_one_le_left hN0.le hM1
      _ = (M*N)^(3*δ) := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le hM1 hN) hδε
  calc
    _ ≤ 2*((Nat.log 2 ⌊N⌋₊ : ℝ)+1)*(D*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N) := hb
    _ ≤ 2*(E*N^δ)*(D*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N) := by gcongr; exact hlog N hN
    _ = (2*E*D)*(N^δ*(M*N)^(2*δ))*sieveRecurrenceShape ξ M N := by ring
    _ ≤ _ := by gcongr

end CubicFirstMoment
end
end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.SieveExponent.recurrence_oai := @OAI.CubicFirstMoment.SieveExponent.recurrence_oai
