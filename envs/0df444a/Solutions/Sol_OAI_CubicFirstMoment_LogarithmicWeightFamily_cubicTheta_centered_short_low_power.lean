-- Prove2me | solution 1 for OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_centered_short_low_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:51:25.967854+00:00
-- url     : https://prove2.me/submissions/12277f34-0fbb-4efd-855f-f16eabae90ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_cubicThetaActualCompletedRadialMain_eq
import Theorems.Thm_OAI_CubicFirstMoment_cubicThetaResidue_radial_voronoi
import Theorems.Thm_OAI_CubicFirstMoment_cubicThetaResidue_voronoi

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_norm {a : Eisenstein} (ha : a ≠ 0) :
    idealExponentNorm (idealExponentOf a) = norm a := by
  unfold idealExponentNorm
  rw [associated_normNat (idealExponentOf_associated ha), normNat_cast]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinHeckeContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contour step for the full smooth character sum. Polynomial
vertical growth is an analytic property of the L-function; the decay,
integrability and vanishing edges are derived for the actual weight. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma mellinEdgeMajorant_integrable (C : ℝ) : Integrable (mellinEdgeMajorant C) := by
  have hi : Integrable (fun t : ℝ => (1+‖t‖)^(-(2:ℝ))) :=
    integrable_one_add_norm (by norm_num)
  convert hi.const_mul C using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  rw [mellinEdgeMajorant, Real.rpow_neg (by positivity), Real.rpow_ofNat,
    Real.norm_eq_abs, div_eq_mul_inv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler products identify and bound the arithmetic Möbius coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

private lemma finiteIdealMoebius_coeff_repeated (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) {q : EisensteinIdealPrime} (hνq : 2 ≤ ν q) :
    MvPowerSeries.coeff ν (finiteIdealMoebius S) = 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty =>
    have hν : ν ≠ 0 := by
      intro h
      have hq := congrArg (fun f : EisensteinIdealExponent => f q) h
      simp only [Finsupp.zero_apply] at hq
      omega
    simp [finiteIdealMoebius, MvPowerSeries.coeff_one, hν]
  | @insert p S hp ih =>
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X]
    by_cases hqp : q = p
    · subst q
      rw [finiteIdealMoebius_coeff_outside S ν hp (by omega),
        ite_eq_left (by omega), finiteIdealMoebius_coeff_outside S _ hp]
      · simp
      · simpa only [Finsupp.tsub_apply, Finsupp.single_eq_same] using
          (show ν p - 1 ≠ 0 by omega)
    · rw [ih ν hνq]
      by_cases hn : 1 ≤ ν p
      · rw [ite_eq_left hn, ih _]
        · simp
        · simpa [Finsupp.tsub_apply, hqp] using hνq
      · simp [hn]

lemma idealMoebiusSeries_repeated {ν : EisensteinIdealExponent}
    {p : EisensteinIdealPrime} (hν : 2 ≤ ν p) :
    MvPowerSeries.coeff ν idealMoebiusSeries = 0 := by
  rw [coeff_idealMoebiusSeries_eq_finite ν.support ν (Finset.Subset.refl _)]
  exact finiteIdealMoebius_coeff_repeated _ _ hν

private lemma finiteIdealMoebius_coeff_squarefree (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hν : ν.support ⊆ S) (h1 : ∀ p, ν p ≤ 1) :
    MvPowerSeries.coeff ν (finiteIdealMoebius S) = (-1 : ℝ) ^ ν.support.card := by
  induction S using Finset.induction_on generalizing ν with
  | empty =>
    have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hν)
    simp [hz, finiteIdealMoebius, MvPowerSeries.coeff_one]
  | @insert p S hp ih =>
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X]
    by_cases hz : ν p = 0
    · have hs : ν.support ⊆ S := by
        intro q hq
        rcases Finset.mem_insert.mp (hν hq) with h | h
        · subst q
          exact (Finsupp.mem_support_iff.mp hq hz).elim
        · exact h
      simpa [hz] using ih ν hs h1
    · have ho : ν p = 1 := by have := h1 p; omega
      let κ : EisensteinIdealExponent := ν - Finsupp.single p 1
      have hk : κ.support = ν.support.erase p := by
        ext q
        by_cases hqp : q = p
        · subst q
          simp [κ, Finsupp.mem_support_iff, Finsupp.tsub_apply, ho]
        · simp [κ, Finsupp.mem_support_iff, Finsupp.tsub_apply, hqp]
      have hκ : κ.support ⊆ S := by
        rw [hk]
        intro q hq
        rcases Finset.mem_erase.mp hq with ⟨hqp, hq⟩
        exact (Finset.mem_insert.mp (hν hq)).resolve_left hqp
      have hκ1 : ∀ q, κ q ≤ 1 := fun q =>
        (Nat.sub_le (ν q) _).trans (h1 q)
      have hcard : κ.support.card + 1 = ν.support.card := by
        rw [hk]
        exact Finset.card_erase_add_one (Finsupp.mem_support_iff.mpr hz)
      rw [finiteIdealMoebius_coeff_outside S ν hp hz, ite_eq_left (by omega),
        ih κ hκ hκ1, zero_sub, ← hcard, pow_succ]
      ring

lemma idealMoebiusSeries_squarefree {ν : EisensteinIdealExponent}
    (h1 : ∀ p, ν p ≤ 1) :
    MvPowerSeries.coeff ν idealMoebiusSeries = (-1 : ℝ) ^ ν.support.card := by
  rw [coeff_idealMoebiusSeries_eq_finite ν.support ν (Finset.Subset.refl _)]
  exact finiteIdealMoebius_coeff_squarefree _ _ (Finset.Subset.refl _) h1

lemma idealExponentOf_support_card {a : Eisenstein} (ha : Squarefree a) :
    (idealExponentOf a).support.card = (UniqueFactorizationMonoid.factors a).card := by
  have hnodup : (Associates.factors' a).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    exact (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha
  change (Associates.factors' a).toFinset.card = _
  rw [Multiset.toFinset_card_of_nodup hnodup]
  have h := congrArg Multiset.card (Associates.map_subtype_coe_factors' (a := a))
  simpa only [Multiset.card_map] using h

/-- The Dirichlet-inverse definition agrees with the repository's
arithmetic Möbius function on every nonzero Eisenstein ideal. -/
lemma idealMoebiusSeries_at_element {a : Eisenstein} (ha : a ≠ 0) :
    MvPowerSeries.coeff (idealExponentOf a) idealMoebiusSeries = (idealMoebius a : ℝ) := by
  by_cases hs : Squarefree a
  · rw [idealMoebiusSeries_squarefree ((idealExponentOf_squarefree_iff ha).mpr hs),
      idealExponentOf_support_card hs]
    simp [idealMoebius, hs]
  · have hh : ¬ ∀ p, idealExponentOf a p ≤ 1 :=
      mt (idealExponentOf_squarefree_iff ha).mp hs
    push Not at hh
    obtain ⟨p, hp⟩ := hh
    rw [idealMoebiusSeries_repeated (by omega : 2 ≤ idealExponentOf a p)]
    simp [idealMoebius, hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite primary ideal polynomials and their actual Eisenstein-element
realizations. These sums omit the ramified prime above three. They are
not identified with the complete ideal series of `IdealMellinSeries`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_primaryIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ primaryIdealBall Y ↔ primary (idealPrimaryGenerator ν) ∧ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha,hN⟩ := mem_primaryElementBall.mp ha
    rw [idealPrimaryGenerator_at_element ha,idealExponentOf_norm (primary_ne_zero ha)]
    exact ⟨ha,hN⟩
  · rintro ⟨hν,hN⟩
    exact Finset.mem_image.mpr ⟨idealPrimaryGenerator ν,
      mem_primaryElementBall.mpr ⟨hν,(idealPrimaryGenerator_norm ν).trans_le hN⟩,
      idealExponentOf_primaryGenerator ν⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler exclusions on the complete ideal lattice. The full norm
ball includes the ramified prime; excluding it is an explicit choice of
prime set, and every rescaling factor is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_fullIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ fullIdealBall Y ↔ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    rw [idealExponentOf_norm (mem_nonzeroNormBall.mp ha).2]
    exact (mem_nonzeroNormBall.mp ha).1
  · intro h
    exact Finset.mem_image.mpr ⟨idealExponentGenerator ν,
      mem_nonzeroNormBall.mpr ⟨by simpa only [idealExponentNorm,normNat_cast] using h,
        idealExponentGenerator_ne_zero ν⟩,idealExponentOf_generator ν⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaBetaComparison
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Beta-integral comparison for the Gamma quotient. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

private lemma beta_real_integral_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in (0:ℝ)..1, t^(x-1)*(1-t)^(y-1)) =
      Real.Gamma x*Real.Gamma y/Real.Gamma (x+y) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (∫ t : ℝ in (0:ℝ)..1, ((t^(x-1)*(1-t)^(y-1):ℝ):ℂ)) =
      Complex.betaIntegral (x:ℂ) (y:ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    simp only [Complex.ofReal_mul,Complex.ofReal_cpow ht.1,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2),Complex.ofReal_sub,Complex.ofReal_one]
  rw [he,Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hx) (by simpa using hy)]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,← Complex.ofReal_add,Complex.Gamma_ofReal]

lemma beta_norm_le_real (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.betaIntegral s (d:ℂ)‖ ≤
      Real.Gamma s.re*Real.Gamma d/Real.Gamma (s.re+d) := by
  rw [← beta_real_integral_eq s.re d hs hd]
  unfold Complex.betaIntegral
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)).trans_eq
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  have hp : 0 < 1-t := sub_pos.mpr ht.2
  rw [show (1:ℂ)-(t:ℂ) = ((1-t:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

lemma gamma_real_shift_ratio_bound (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.Gamma s‖/‖Complex.Gamma (s+(d:ℂ))‖ ≤
      Real.Gamma s.re/Real.Gamma (s.re+d) := by
  have h := beta_norm_le_real s hs hd
  have hg : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hs (by simpa using hd),
    norm_div,norm_mul,Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hg] at h
  apply (mul_le_mul_iff_right₀ hg).mp
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

lemma gamma_shift_ratio_bound (x y t : ℝ) (n : ℕ) (hx : 0 < x)
    (hgap : 0 < y+(n:ℝ)-x) :
    ‖Complex.Gamma ((x:ℂ)+(t:ℂ)*Complex.I) /
      Complex.Gamma ((y:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (Real.Gamma x/Real.Gamma (y+n))*
        ‖(ascPochhammer ℂ n).eval ((y:ℂ)+(t:ℂ)*Complex.I)‖ := by
  let z : ℂ := (y:ℂ)+(t:ℂ)*Complex.I
  let w : ℂ := (x:ℂ)+(t:ℂ)*Complex.I
  have hyn : 0 < y+(n:ℝ) := by linarith
  have hGn : Complex.Gamma (z+n) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa [z] using hyn)
  by_cases hG : Complex.Gamma z = 0
  · change ‖Complex.Gamma w/Complex.Gamma z‖ ≤ _
    rw [hG,div_zero,norm_zero]
    exact mul_nonneg (div_nonneg (Real.Gamma_pos_of_pos hx).le
      (Real.Gamma_pos_of_pos hyn).le) (_root_.norm_nonneg _)
  have hreg : ∀ k : ℕ, z ≠ -(k:ℂ) := by
    intro k hk
    exact hG (by rw [hk,Complex.Gamma_neg_nat_eq_zero])
  have hp := congrArg (fun u : ℂ => ‖u‖) (Complex.Gamma_add_nat_div_Gamma_eq (n := n) z hreg)
  rw [norm_div] at hp
  have hshift : w+((y+(n:ℝ)-x:ℝ):ℂ) = z+n := by dsimp [w,z]; push_cast; ring
  have hb := gamma_real_shift_ratio_bound w (by simpa [w] using hx) hgap
  rw [hshift,show w.re=x by simp [w],show x+(y+(n:ℝ)-x)=y+n by ring] at hb
  change ‖Complex.Gamma w/Complex.Gamma z‖ ≤ _
  rw [norm_div]
  calc
    _ = (‖Complex.Gamma w‖/‖Complex.Gamma (z+n)‖)*
        ‖(ascPochhammer ℂ n).eval z‖ := by
      rw [← hp]
      field_simp [norm_ne_zero_iff.mpr hG,norm_ne_zero_iff.mpr hGn]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaQuotientGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-strip Gamma quotient follows from the Beta integral and
integer recurrence, with the fixed angular shift retained. -/
noncomputable section
open Set
namespace CubicFirstMoment

private lemma pochhammer_norm_bound (n : ℕ) (z : ℂ) :
    ‖(ascPochhammer ℂ n).eval z‖ ≤ (‖z‖+(n:ℝ))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,norm_mul]
    have hn : ‖z+(n:ℂ)‖ ≤ ‖z‖+(n:ℝ) := by simpa using norm_add_le z (n:ℂ)
    calc
      _ ≤ (‖z‖+(n:ℝ))^n*(‖z‖+(n:ℝ)) :=
        mul_le_mul ih hn (_root_.norm_nonneg _) (by positivity)
      _ = (‖z‖+(n:ℝ))^(n+1) := (pow_succ _ _).symm
      _ ≤ (‖z‖+((n+1:ℕ):ℝ))^(n+1) := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith

private lemma gamma_positive_ratio_compact {a k : ℝ} (hk : -(1/2:ℝ) < k)
    (n : ℕ) (hn : 1-2*a < (n:ℝ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ σ ∈ Icc a (1/2:ℝ),
      Real.Gamma (1-σ+k)/Real.Gamma (σ+k+n) ≤ M := by
  let F : ℝ → ℂ := fun σ => Complex.Gamma ((1-σ+k:ℝ):ℂ)/
    Complex.Gamma ((σ+k+n:ℝ):ℂ)
  have hx {σ : ℝ} (hσ : σ ∈ Icc a (1/2:ℝ)) : 0 < 1-σ+k := by linarith [hσ.2]
  have hy {σ : ℝ} (hσ : σ ∈ Icc a (1/2:ℝ)) : 0 < σ+k+n := by linarith [hσ.1,hσ.2]
  have hc : ContinuousOn F (Icc a (1/2:ℝ)) := by
    intro σ hσ
    have hreg {x : ℝ} (hp : 0 < x) : ∀ m : ℕ, (x:ℂ) ≠ -(m:ℂ) := by
      intro m hm
      have hr := congrArg Complex.re hm
      simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at hr
      have : (0:ℝ) ≤ m := by positivity
      linarith
    apply ContinuousAt.continuousWithinAt
    have ht : ContinuousAt (fun τ : ℝ => Complex.Gamma ((1-τ+k:ℝ):ℂ)) σ :=
      (Complex.continuousAt_Gamma _ (hreg (hx hσ))).comp
        (f := fun τ : ℝ => ((1-τ+k:ℝ):ℂ)) (by fun_prop)
    have hb : ContinuousAt (fun τ : ℝ => Complex.Gamma ((τ+k+n:ℝ):ℂ)) σ :=
      (Complex.continuousAt_Gamma _ (hreg (hy hσ))).comp
        (f := fun τ : ℝ => ((τ+k+n:ℝ):ℂ)) (by fun_prop)
    exact ht.div hb
      (Complex.Gamma_ne_zero_of_re_pos (s := ((σ+k+n:ℝ):ℂ)) (by simpa using hy hσ))
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro σ hσ
  have he : ‖F σ‖ = Real.Gamma (1-σ+k)/Real.Gamma (σ+k+n) := by
    dsimp [F]
    rw [norm_div,Complex.Gamma_ofReal,Complex.Gamma_ofReal,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (hx hσ)),abs_of_pos (Real.Gamma_pos_of_pos (hy hσ))]
  rw [← he]
  exact (hM σ hσ).trans (le_max_left _ _)

/-- The exact fixed-angular quotient input used by the conditional proof. -/
theorem angularGammaQuotientStripBound_proved (k a : ℝ) (hk : -(1/2:ℝ) < k) :
    AngularGammaQuotientStripBound k a := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1-2*a)
  obtain ⟨M,hM,hbound⟩ := gamma_positive_ratio_compact hk n hn
  let D := |a+k|+|(1/2:ℝ)+k|+(n:ℝ)+1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨M*D^n,n,mul_nonneg hM.le (pow_nonneg hD.le _),?_⟩
  intro σ hσ t
  have hx : 0 < 1-σ+k := by linarith [hσ.2]
  have hgap : 0 < (σ+k)+(n:ℝ)-(1-σ+k) := by linarith [hσ.1]
  have hb := gamma_shift_ratio_bound (1-σ+k) (σ+k) t n hx hgap
  have hnum : 1-((σ:ℂ)+(t:ℂ)*Complex.I)+(k:ℂ) =
      starRingEnd ℂ (((1-σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I) := by
    apply Complex.ext <;> simp
  have hden : (σ:ℂ)+(t:ℂ)*Complex.I+(k:ℂ) =
      ((σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I := by push_cast; ring
  have ha : |σ+k| ≤ |a+k|+|(1/2:ℝ)+k| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (a+k),abs_nonneg ((1/2:ℝ)+k),hσ.1]
    · linarith [le_abs_self ((1/2:ℝ)+k),abs_nonneg (a+k),hσ.2]
  have hz : ‖((σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I‖ ≤ |σ+k|+|t| := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,mul_one]
      using norm_add_le (((σ+k:ℝ):ℂ)) ((t:ℂ)*Complex.I)
  have hpoly : ‖(ascPochhammer ℂ n).eval (((σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I)‖ ≤
      D^n*(1+|t|)^n := by
    apply (pochhammer_norm_bound _ _).trans
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hD1 : 1 ≤ D := by
      dsimp [D]
      linarith [abs_nonneg (a+k),abs_nonneg ((1/2:ℝ)+k),show (0:ℝ) ≤ n by positivity]
    dsimp [D] at *
    nlinarith [abs_nonneg t,abs_nonneg (a+k),abs_nonneg ((1/2:ℝ)+k),
      show (0:ℝ) ≤ n by positivity]
  unfold angularGammaFEQuotient
  rw [hnum,hden,Complex.Gamma_conj,norm_div,Complex.norm_conj]
  rw [norm_div] at hb
  apply hb.trans
  calc
    _ ≤ M*(D^n*(1+|t|)^n) :=
      mul_le_mul (hbound σ hσ) hpoly (_root_.norm_nonneg _) hM.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor and pair-product multiplicities with a bounded number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_inj_primary {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : idealExponentOf a = idealExponentOf b) : a = b := by
  have hA := idealExponentOf_associated (primary_ne_zero ha)
  have hB := idealExponentOf_associated (primary_ne_zero hb)
  rw [h] at hA
  exact primary_associated_eq ha hb (hA.symm.trans hB)

lemma primary_divisor_card_exponents (T : Finset Eisenstein)
    (hT : ∀ a ∈ T, primary a) {b : Eisenstein} (hb : b ≠ 0) :
    (T.filter (fun a => a ∣ b)).card ≤
      ∏ p ∈ (idealExponentOf b).support, (idealExponentOf b p + 1) := by
  let D := T.filter (fun a => a ∣ b)
  have hinj : Set.InjOn idealExponentOf (D : Set Eisenstein) := by
    intro a ha c hc he
    exact idealExponentOf_inj_primary (hT a (Finset.mem_filter.mp ha).1)
      (hT c (Finset.mem_filter.mp hc).1) he
  have hsub : D.image idealExponentOf ⊆ Finset.Iic (idealExponentOf b) := by
    intro ν hν
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hν
    exact Finset.mem_Iic.mpr (idealExponentOf_le_of_dvd
      (primary_ne_zero (hT a (Finset.mem_filter.mp ha).1)) hb (Finset.mem_filter.mp ha).2)
  calc
    D.card = (D.image idealExponentOf).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Iic (idealExponentOf b)).card := Finset.card_le_card hsub
    _ = _ := by rw [Finsupp.card_Iic]; simp

lemma idealPrimeRepresentative_normNat_ge_two (p : EisensteinIdealPrime) :
    2 ≤ normNat (idealPrimeRepresentative p) := by
  have hp := idealPrimeRepresentative_irreducible p
  have hz := normNat_ne_zero hp.ne_zero
  have ho : normNat (idealPrimeRepresentative p) ≠ 1 := by
    intro h
    apply hp.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [← normNat_cast, h]
    norm_num
  omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDivisorPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary-exponent ideal divisor bounds for the short-convolution
polynomials. No bound on the number of distinct prime bases is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma exponent_add_one_le_two_pow (n : ℕ) : (n : ℝ)+1 ≤ (2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have hnon : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
    nlinarith

private lemma exponent_factor_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n : ℕ, (n:ℝ)+1 ≤ A*(2:ℝ)^(ε*n) := by
  let L : ℝ := ε*Real.log 2
  have hL : 0 < L := mul_pos hε (Real.log_pos (by norm_num))
  refine ⟨1+1/L,by linarith [div_pos (zero_lt_one : (0:ℝ) < 1) hL],?_⟩
  intro n
  have hE1 : 1 ≤ Real.exp (L*n) := Real.one_le_exp_iff.mpr (by positivity)
  have hn : (n:ℝ) ≤ Real.exp (L*n)/L := by
    apply (le_div_iff₀ hL).mpr
    nlinarith [Real.add_one_le_exp (L*n)]
  have hE : Real.exp (L*n) = (2:ℝ)^(ε*n) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    dsimp [L]
    congr 1
    ring
  calc
    _ ≤ Real.exp (L*n)/L+Real.exp (L*n) := add_le_add hn hE1
    _ = (1+1/L)*Real.exp (L*n) := by ring
    _ = _ := by rw [hE]

/-- The full ideal divisor product is bounded by every positive norm
power. Small prime ideals form a finite set, while large prime ideals
absorb every exponent directly. -/
theorem ideal_divisor_product_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : EisensteinIdealExponent,
      (∏ p ∈ ν.support, ((ν p:ℝ)+1)) ≤ C*idealExponentNorm ν^ε := by
  obtain ⟨A,hA,hA_bound⟩ := exponent_factor_uniform hε
  let R : ℝ := (2:ℝ)^(1/ε)
  let T : Finset EisensteinIdealPrime :=
    (fullIdealBall R).biUnion (fun ν => ν.support)
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num),one_div_mul_cancel hε.ne',Real.rpow_one]
  have hT (p : EisensteinIdealPrime) :
      (normNat (idealPrimeRepresentative p):ℝ) ≤ R → p ∈ T := by
    intro hp
    apply Finset.mem_biUnion.mpr
    refine ⟨Finsupp.single p 1,?_,by simp⟩
    apply mem_fullIdealBall.mpr
    simpa only [idealExponentNorm_single,pow_one] using hp
  refine ⟨A^T.card,pow_pos (zero_lt_one.trans_le hA) _,?_⟩
  intro ν
  have hpoint : ∀ p ∈ ν.support, (ν p:ℝ)+1 ≤
      (if p ∈ T then A else 1)*(normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p) := by
    intro p hp
    have hNp : (2:ℝ) ≤ normNat (idealPrimeRepresentative p) := by
      exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
    by_cases hpT : p ∈ T
    · simp only [ite_eq_left hpT]
      exact (hA_bound (ν p)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by norm_num) hNp (by positivity)) (zero_le_one.trans hA))
    · simp only [ite_eq_right hpT,one_mul]
      have hRp : R ≤ (normNat (idealPrimeRepresentative p):ℝ) := le_of_lt
        (lt_of_not_ge (fun h => hpT (hT p h)))
      have hbase : (2:ℝ) ≤ (normNat (idealPrimeRepresentative p):ℝ)^ε := by
        rw [← hRe]
        exact Real.rpow_le_rpow hR.le hRp hε.le
      calc
        _ ≤ (2:ℝ)^ν p := exponent_add_one_le_two_pow _
        _ ≤ ((normNat (idealPrimeRepresentative p):ℝ)^ε)^ν p :=
          pow_le_pow_left₀ (by norm_num) hbase _
        _ = _ := by rw [← Real.rpow_mul_natCast (by positivity)]
  have hprod := Finset.prod_le_prod (s := ν.support)
    (fun p _ => (by positivity : 0 ≤ (ν p:ℝ)+1)) hpoint
  rw [Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ ν.support, if p ∈ T then A else 1) ≤ A^T.card := by
    rw [Finset.prod_ite_mem,Finset.prod_const]
    exact pow_le_pow_right₀ hA (Finset.card_le_card Finset.inter_subset_right)
  have hnorm : (∏ p ∈ ν.support,
      (normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p)) = idealExponentNorm ν^ε := by
    calc
      _ = ∏ p ∈ ν.support, ((normNat (idealPrimeRepresentative p):ℝ)^ν p)^ε := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
        congr 1
        ring
      _ = (∏ p ∈ ν.support, (normNat (idealPrimeRepresentative p):ℝ)^ν p)^ε :=
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity) ε
      _ = _ := by rw [idealExponentNorm_eq_prod]
  rw [hnorm] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le _))

/-- Arbitrary primary divisors, with no squarefree or bounded-prime-support
restriction on the ambient element. -/
theorem primary_divisor_card_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset Eisenstein),
      (∀ a ∈ T, primary a) → ∀ b : Eisenstein, b ≠ 0 →
      ((T.filter (fun a => a ∣ b)).card : ℝ) ≤ C*norm b^ε := by
  obtain ⟨C,hC,hbound⟩ := ideal_divisor_product_small_power hε
  refine ⟨C,hC,?_⟩
  intro T hT b hb
  have h : ((T.filter (fun a => a ∣ b)).card : ℝ) ≤
      ((∏ p ∈ (idealExponentOf b).support, (idealExponentOf b p+1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (primary_divisor_card_exponents T hT hb)
  push_cast at h
  exact h.trans ((hbound (idealExponentOf b)).trans_eq (by rw [idealExponentOf_norm hb]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeightFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Mellin estimates for the smooth weight families occurring in
Type I. The hypotheses state common support and derivative bounds in
logarithmic coordinates. No transform or moment estimate is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform BigOperators
namespace CubicFirstMoment

private lemma weight_exp_derivative_bound {M R σ u : ℝ} (hM : 0 ≤ M)
    (hσ : |σ| ≤ M) (hu : |u| ≤ R) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
      M^n * Real.exp (M*R) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_exp_const_mul]
  simp only [norm_mul,Real.norm_eq_abs,abs_pow,abs_neg,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ n) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  calc
    -σ*u ≤ |-σ*u| := le_abs_self _
    _ = |σ| *|u| := by rw [abs_mul,abs_neg]
    _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM

lemma UniformLogWeights.log_seminorms {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i σ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n
        (mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) ≤ C := by
  choose B hB hder using h.derivative_bound
  let M' := max M 0
  let A := ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*
    (M'^j*Real.exp (M'*h.radius))*B (n-j)
  have hM : 0 ≤ M' := le_max_right _ _
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j hj => by
    have hjB := hB (n-j)
    positivity)
  refine ⟨h.radius^k*A,mul_nonneg (pow_nonneg h.radius_nonneg _) hA,?_⟩
  intro i σ hσ
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (pow_nonneg h.radius_nonneg _) hA)
  intro u
  by_cases hu : |u| ≤ h.radius
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hw : ContDiff ℝ ∞ (fun v : ℝ => W i (Real.exp (-v))) :=
      (h.smooth i).comp (Real.contDiff_exp.comp contDiff_id.neg)
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he hw u (n := n) (mod_cast le_top)
    have hb : ‖iteratedFDeriv ℝ n
        (mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) u‖ ≤ A := by
      change ‖iteratedFDeriv ℝ n (fun v : ℝ =>
        Real.exp (-σ*v) • W i (Real.exp (-v))) u‖ ≤ A
      apply hd.trans
      apply Finset.sum_le_sum
      intro j hj
      have hjB := hB (n-j)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (weight_exp_derivative_bound hM (hσ.trans (le_max_left _ _)) hu j) (by positivity)
      · exact hder (n-j) i u
      · positivity
      · positivity
    simpa only [Real.norm_eq_abs] using
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu k) hb
        (_root_.norm_nonneg _) (pow_nonneg h.radius_nonneg _)
  · have hz : iteratedFDeriv ℝ n
        (mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) u = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W i (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W i (Real.exp (-v))) hs
      exact hu (h.support_bound i u hs')
    rw [hz,norm_zero,mul_zero]
    exact mul_nonneg (pow_nonneg h.radius_nonneg _) hA

lemma UniformLogWeights.vertical_bounded {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) :
    Bornology.IsVonNBounded ℝ
      ((fun p : ι × ℝ => mellinVerticalSchwartz (W p.1) (h.compact p.1)
        (h.positive p.1) (h.smooth p.1) p.2) '' {p | |p.2| ≤ M}) := by
  let f : ι × ℝ → 𝓢(ℝ,ℂ) := fun p =>
    mellinLogSchwartz (W p.1) (h.compact p.1) (h.positive p.1) (h.smooth p.1) p.2
  have hb : Bornology.IsVonNBounded ℝ (f '' {p | |p.2| ≤ M}) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro a
    obtain ⟨C,hC,hbound⟩ := h.log_seminorms M a.1 a.2
    exact ⟨C+1,by linarith,fun p hp => (hbound p.1 p.2 hp).trans_lt (by linarith)⟩
  let L : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.compCLM ℝ (by
      simp only [div_eq_mul_inv]
      fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
      mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)
  convert hb.image L using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Set.image_comp]
  rfl

/-- Uniform rapid decay, derived from support and derivative bounds. -/
theorem UniformLogWeights.mellin_decay {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i σ, |σ| ≤ M → ∀ t : ℝ,
      (1+|t|)^A*‖mellin (W i) ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_finset_seminorm_bounded
      (fun p : ι × ℝ => mellinVerticalSchwartz (W p.1) (h.compact p.1)
        (h.positive p.1) (h.smooth p.1) p.2) |>.mp (h.vertical_bounded M) (Finset.Iic (A,0))
  refine ⟨2^A*C,by positivity,?_⟩
  intro i σ hσ t
  have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl
      (mellinVerticalSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) t
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mellinVerticalSchwartz_apply] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (hb (i,σ) hσ).le (by positivity))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed angular multipliers are precisely powers of the actual
complex Fourier frequency and its conjugate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_div_nine (n : Eisenstein) :
    cubicThetaFrequency n=(n:ℂ)/9 := by
  have hs : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun n : Eisenstein => (n:ℂ)) lambdaE_sq
    push_cast at he
    rw [lambdaE_coe] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
  have h4 : traceLambda^4=(9:ℂ) := by
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  simp only [cubicThetaFrequency,h4]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invariance of the cubic multiplier under the two integral modular
generators, as needed to extend it to the group of DR v3 Section 5.1. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaKubotaConjugate_S_entries (g : cubicThetaPrincipalGroup) :
    (cubicThetaKubotaConjugate cubicThetaModularS g).val 0 0 = g.val 1 1 ∧
      (cubicThetaKubotaConjugate cubicThetaModularS g).val 1 0 = -g.val 0 1 := by
  change ((!![0,-1;1,0] * (g.val:Matrix (Fin 2) (Fin 2) Eisenstein)) *
      Matrix.adjugate !![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein) 0 0 = g.val 1 1 ∧
    ((!![0,-1;1,0] * (g.val:Matrix (Fin 2) (Fin 2) Eisenstein)) *
      Matrix.adjugate !![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein) 1 0 = -g.val 0 1
  constructor <;> simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem cubicThetaKubotaValue_conjugate_S (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (cubicThetaKubotaConjugate cubicThetaModularS g) =
      cubicThetaKubotaValue g := by
  obtain ⟨ha,hc⟩ := cubicThetaKubotaConjugate_S_entries g
  rw [cubicThetaKubotaValue_eq_symbol,ha,hc,
    cubicSymbol_neg (cubicThetaPrincipalGroup_diagonal_primary g).2,
    ←cubicThetaKubota_column_switch,cubicThetaKubotaValue_eq_symbol]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspTypes
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three translated inversion types needed for primary bottom rows.
The actual constant is retained at the trivial type. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFullTranslation_add (a b : Eisenstein) :
    cubicThetaFullTranslation (a+b)=cubicThetaFullTranslation a*cubicThetaFullTranslation b := by
  apply Subtype.ext
  change (!![1,a+b;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,a;0,1]*!![1,b;0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma cubicThetaShiftedInversion_factor (b : Eisenstein) :
    cubicThetaShiftedInversion b=cubicThetaFullTranslation b*cubicThetaFullInversion := by
  apply Subtype.ext
  change (!![b,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,b;0,1]*!![0,-1;1,0]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual three cusp multipliers agree when the lower-right entry is
zero modulo three. This is the elementary supplementary-law step needed
before finite Ramanujan summation. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimaryBottom_multiplier_symbol (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)=
      cubicSymbol (1+g 0 1*(g 1 0-1)) (g 1 1*(g 1 0-1)) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol ((cubicThetaPrimaryBottomDefect g).val 0 0)
    ((cubicThetaPrimaryBottomDefect g).val 1 0)=_
  rw [cubicThetaPrimaryBottomDefect_matrix]
  rfl

lemma cubicThetaProjectedCuspMatrix_entries (g : SL(2,Eisenstein)) (j : Fin 3) :
    cubicThetaProjectedCuspMatrix g j 0 1=g 0 1+(j.val:Eisenstein)*omegaE*g 1 1 ∧
    cubicThetaProjectedCuspMatrix g j 1 0=g 1 0 ∧
    cubicThetaProjectedCuspMatrix g j 1 1=g 1 1 := by
  change ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 0 1=_ ∧
    ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 0=_ ∧
    ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 1=_
  simp [Matrix.mul_apply,Fin.sum_univ_two]

theorem cubicThetaProjectedCuspMultiplier_constant (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (hd : (3:Eisenstein)∣g 1 1) (j : Fin 3) :
    cubicThetaProjectedCuspMultiplier g hc j=
      cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc) := by
  have hj := cubicThetaProjectedCuspMatrix_entries g j
  have hpj := (cubicThetaPrincipalGroup_diagonal_primary
    (cubicThetaPrimaryBottomPrincipal (cubicThetaProjectedCuspMatrix g j)
      (cubicThetaProjectedCuspMatrix_primary g hc j))).1
  have hp := (cubicThetaPrincipalGroup_diagonal_primary (cubicThetaPrimaryBottomPrincipal g hc)).1
  change primary ((cubicThetaPrimaryBottomDefect (cubicThetaProjectedCuspMatrix g j)).val 0 0) at hpj
  change primary ((cubicThetaPrimaryBottomDefect g).val 0 0) at hp
  rw [cubicThetaPrimaryBottomDefect_matrix] at hpj hp
  change primary (1+cubicThetaProjectedCuspMatrix g j 0 1*
    (cubicThetaProjectedCuspMatrix g j 1 0-1)) at hpj
  change primary (1+g 0 1*(g 1 0-1)) at hp
  rw [hj.1,hj.2.1] at hpj
  unfold cubicThetaProjectedCuspMultiplier
  rw [cubicThetaPrimaryBottom_multiplier_symbol,cubicThetaPrimaryBottom_multiplier_symbol,
    hj.1,hj.2.1,hj.2.2]
  apply cubicSymbol_periodic_of_nine_and_numerator hpj hp
  · obtain ⟨d,hd⟩ := hd
    obtain ⟨c,hc⟩ := hc
    refine ⟨(j.val:Eisenstein)*omegaE*d*c,?_⟩
    rw [hd,hc]
    ring
  · refine ⟨(j.val:Eisenstein)*omegaE,?_⟩
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAdaptedMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A principal-level decomposition evaluates the common multiplier for
cusp lifts with both diagonal entries zero modulo three. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaFullTranslation_neg (a : Eisenstein) :
    cubicThetaFullTranslation (-a)=(cubicThetaFullTranslation a)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [←cubicThetaFullTranslation_add,neg_add_cancel]
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

lemma cubicThetaRightInversion_value (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) :
    cubicThetaKubotaValue (cubicThetaRightInversionPrincipal g hc ha hd)=
      cubicSymbol (g 1 0) (g 0 0) := by
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubota_column_switch]
  change cubicSymbol ((g*cubicThetaFullInversion⁻¹).val 1 1)
    ((g*cubicThetaFullInversion⁻¹).val 0 1)=_
  rw [cubicThetaRightInversion_matrix]
  rfl

theorem cubicThetaPrimaryBottom_multiplier_adapted (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) :
    cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)=
      cubicSymbol (g 1 0) (g 0 0) := by
  obtain ⟨a,ha'⟩ := ha
  obtain ⟨d,hd'⟩ := hd
  let h := cubicThetaRightInversionPrincipal g hc ⟨a,ha'⟩ ⟨d,hd'⟩
  let k := cubicThetaKubotaConjugate cubicThetaModularS (cubicThetaPrincipalTranslation (-d))
  let l := cubicThetaPrincipalTranslation (-a)
  have he : cubicThetaPrimaryBottomPrincipal g hc=h*k*l := by
    apply Subtype.ext
    change g*(cubicThetaPrimaryBottomSeed g)⁻¹=
      (g*cubicThetaFullInversion⁻¹)*
        (cubicThetaModularS*(cubicThetaPrincipalTranslation (-d)).val*cubicThetaModularS⁻¹)*
          (cubicThetaPrincipalTranslation (-a)).val
    have hS : cubicThetaModularS=cubicThetaFullInversion := rfl
    have htd : (cubicThetaPrincipalTranslation (-d)).val=
        (cubicThetaFullTranslation (3*d))⁻¹ := by
      change cubicThetaFullTranslation (3*(-d))=_
      rw [mul_neg,cubicThetaFullTranslation_neg]
    have hta : (cubicThetaPrincipalTranslation (-a)).val=
        (cubicThetaFullTranslation (3*a))⁻¹ := by
      change cubicThetaFullTranslation (3*(-a))=_
      rw [mul_neg,cubicThetaFullTranslation_neg]
    rw [cubicThetaPrimaryBottomSeed,cubicThetaShiftedInversion_factor,ha',hd',hS,htd,hta]
    group
  rw [he,cubicThetaKubotaValue_mul,cubicThetaKubotaValue_mul]
  have hk : cubicThetaKubotaValue k=1 := by
    rw [show k=cubicThetaKubotaConjugate cubicThetaModularS (cubicThetaPrincipalTranslation (-d)) from rfl,
      cubicThetaKubotaValue_conjugate_S,cubicThetaPrincipalTranslation_value]
  rw [hk,show cubicThetaKubotaValue l=1 from cubicThetaPrincipalTranslation_value _,mul_one,mul_one]
  exact cubicThetaRightInversion_value g hc _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticCubeScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube multiplication in the literal Patterson coefficient formula,
including its unit and ramified cases. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaCoordinates.amplitude_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    (R.mulPrimaryCube e he).amplitude=R.amplitude/norm e := by
  change 3^(4-((R.order/3:ℕ):ℝ))/(Real.sqrt (norm R.squarefreePart)*norm (R.cubePart*e))=
    (3^(4-((R.order/3:ℕ):ℝ))/(Real.sqrt (norm R.squarefreePart)*norm R.cubePart))/norm e
  rw [norm_mul_eq,div_div]
  congr 1
  ring

lemma CubicThetaCoordinates.coefficient_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    (R.mulPrimaryCube e he).coefficient=(norm e:ℂ)⁻¹*R.coefficient := by
  unfold coefficient
  rw [R.amplitude_mulPrimaryCube]
  dsimp only [mulPrimaryCube]
  push_cast
  split_ifs <;> ring

theorem cubicThetaArithmeticCoefficient_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    cubicThetaArithmeticCoefficient (n*e^3)=(norm e:ℂ)⁻¹*cubicThetaArithmeticCoefficient n := by
  rw [cubicThetaArithmeticCoefficient_formula (R.mulPrimaryCube e he),
    cubicThetaArithmeticCoefficient_formula R,R.coefficient_mulPrimaryCube]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspPeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three actual cusp coefficient families depend only on the integer
cusp index modulo three. This is inherited from their literal support. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspIndex_congr {x y : Eisenstein} (h : (3:Eisenstein)∣x-y) :
    (3:ℤ)∣cubicThetaCuspIndex x-cubicThetaCuspIndex y := by
  obtain ⟨t,ht⟩ := h
  refine ⟨cubicThetaCuspIndex t,?_⟩
  have he : x-y=(3:ℤ) • t := by simpa only [zsmul_eq_mul,Int.cast_ofNat] using ht
  have hh := congrArg (fun z : Eisenstein => coordinatesEquiv.symm z 1) he
  simpa only [cubicThetaCuspIndex,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul] using hh

lemma cubicThetaCuspIndex_omega (j : ℤ) :
    cubicThetaCuspIndex ((j:Eisenstein)*omegaE)=j := by
  have he : coordinatesEquiv ![(0:ℤ),j]=(j:Eisenstein)*omegaE := by
    change ofCoords 0 j=_
    simp [ofCoords]
  unfold cubicThetaCuspIndex
  rw [←he,LinearEquiv.symm_apply_apply]
  rfl

lemma cubicThetaActualCuspCoefficient_periodic {m n : ℤ} (h : (3:ℤ)∣n-m) :
    cubicThetaActualCuspCoefficient n=cubicThetaActualCuspCoefficient m := by
  have he : (3:ℤ)∣n ↔ (3:ℤ)∣m := by
    constructor
    · intro hn
      have hm := dvd_sub hn h
      simpa only [sub_sub_cancel] using hm
    · intro hm
      have hn := dvd_add h hm
      simpa only [sub_add_cancel] using hn
  by_cases hn : (3:ℤ)∣n
  · simp only [cubicThetaActualCuspCoefficient,hn,he.mp hn,ite_true, if_true]
  · have hm := mt he.mpr hn
    simp only [cubicThetaActualCuspCoefficient,hn,hm,ite_false, if_false]
    funext k
    unfold cubicThetaShiftedLatticeCoefficient
    have hnm : lambdaE∣(n:Eisenstein)-(m:Eisenstein) := by
      obtain ⟨t,ht⟩ := h
      have hl : lambdaE∣(3:Eisenstein) := ⟨-lambdaE,by
        rw [mul_neg,←pow_two,lambdaE_sq,neg_neg]⟩
      apply dvd_trans hl
      exact ⟨(t:Eisenstein),by exact_mod_cast ht⟩
    have hiff : lambdaE∣k-(n:Eisenstein) ↔ lambdaE∣k-(m:Eisenstein) := by
      constructor
      · intro hk
        convert dvd_add hk hnm using 1
        all_goals try with_reducible_and_instances rfl
        ring
      · intro hk
        convert dvd_sub hk hnm using 1
        all_goals try with_reducible_and_instances rfl
        ring
    rw [hiff]

lemma cubicThetaProjectedCuspType_congr (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0) (j : Fin 3) :
    (3:ℤ)∣cubicThetaProjectedCuspType g j-(j.val:ℤ) := by
  have hj : cubicThetaProjectedCuspMatrix g j 0 0=
      g 0 0+(j.val:Eisenstein)*omegaE*g 1 0 := by
    change ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 0 0=_
    simp [Matrix.mul_apply,Fin.sum_univ_two]
  have h : (3:Eisenstein)∣cubicThetaProjectedCuspMatrix g j 0 0-(j.val:Eisenstein)*omegaE := by
    rw [hj]
    convert dvd_add ha (dvd_mul_of_dvd_right hc ((j.val:Eisenstein)*omegaE)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hh := cubicThetaCuspIndex_congr h
  have hjindex : cubicThetaCuspIndex ((j.val:Eisenstein)*omegaE)=(j.val:ℤ) := by
    simpa only [Int.cast_natCast] using cubicThetaCuspIndex_omega (j.val:ℤ)
  rw [hjindex] at hh
  exact hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLevelAngularReciprocity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put every genuine signed angular transformation on the symmetric height scale. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaLevelScale_square (q : Eisenstein) :
    cubicThetaLevelScale q^2=(norm q)⁻¹ := by
  unfold cubicThetaLevelScale
  rw [inv_pow,Real.sq_sqrt (norm_nonneg q)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-angular metaplectic inputs, stated for the literal Gauss series.

Sources: Heath-Brown, *Kummer's conjecture for cubic Gauss sums* (2000),
§3 Lemma 3 (author manuscript p.9), with angular index zero; Dunn–Radziwiłł,
*Bias in cubic Gauss sums* (2024), arXiv:2109.07463v3, Proposition 5.2,
pp.29–30. No Type-I estimate or Mellin contour identity is an input here. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_norm_rpow_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun u : PrimaryArgument => norm u^(-s)) :=
  (summable_eisenstein_norm_rpow hs).subtype _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal level/angular Voronoi input of Dunn--Radziwill,
arXiv:2109.07463v3, Proposition 5.3, equations (5.79)--(5.82), pp.33--34.
The raw formula is kept separate from its proved Gauss/phase normalization.
The index `n` below denotes the actual frequency `n / lambda`; zero is excluded.
No estimate for a completed sum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticFrequency_ne_zero (n : MetaplecticDualArgument) :
    metaplecticFrequency n ≠ 0 :=
  div_ne_zero (fun h => n.property (Subtype.ext h)) traceLambda_ne_zero

lemma norm_metaplecticLocalCoefficient_le {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) :
    ‖metaplecticLocalCoefficient r n‖ ≤ metaplecticCommonNorm r n := by
  rw [metaplecticLocalCoefficient,norm_prod]
  have hp (p : Eisenstein) (hp : p ∈ primaryPrimeFactors r) : 1 ≤ norm p :=
    one_le_norm (primaryPrimeFactor_spec hr hp).1.2.ne_zero
  calc
    _ ≤ ∏ p ∈ primaryPrimeFactors r, if p ∣ n.val then norm p else 1 := by
      apply Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _)
      intro p hpm
      split_ifs with h
      · simp only [Complex.norm_real,Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith [hp p hpm])]
        linarith
      · norm_num
    _ = metaplecticCommonNorm r n := by
      simp only [metaplecticCommonNorm,Finset.prod_ite,Finset.prod_const_one,mul_one]

lemma metaplecticCompleted_eq_raw {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) :
    metaplecticCompleted r ℓ W X = gauss r*theta ℓ r*metaplecticRawCompleted r ℓ W X := by
  rw [metaplecticCompleted,metaplecticRawCompleted,← tsum_mul_left]
  apply tsum_congr
  intro du
  split_ifs
  · rw [gauss_mul hr du.2.property,theta_mul,cubic_reciprocity du.2.property hr]
    ring
  · ring

lemma gauss_mul_conj_unnormalized {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    gauss r*star ((Real.sqrt (norm r):ℂ)*gauss r) = (Real.sqrt (norm r):ℂ) := by
  rw [star_mul]
  simp only [Complex.star_def,Complex.conj_ofReal]
  calc
    _ = (Real.sqrt (norm r):ℂ)*(gauss r*(starRingEnd ℂ) (gauss r)) := by ring
    _ = _ := by
      rw [Complex.mul_conj',norm_gauss_of_squarefree hr hs]
      norm_num

lemma angular_conjugate_ratio {r : Eisenstein} (hr : r ≠ 0) (ℓ : ℤ) :
    theta ℓ r*((star (r:ℂ)/(r:ℂ))^(-ℓ)) = theta (3*ℓ) r := by
  have hz : (r:ℂ) ≠ 0 := fun h => hr (Subtype.ext h)
  have hn : (‖(r:ℂ)‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hratio : star (r:ℂ)/(r:ℂ) = ((r:ℂ)/(‖(r:ℂ)‖:ℂ))^(-2:ℤ) := by
    rw [zpow_neg,zpow_ofNat,← inv_pow,inv_div]
    field_simp
    simpa [pow_two,mul_comm] using (Complex.mul_conj' (r:ℂ))
  rw [hratio,← zpow_mul]
  simp only [theta]
  rw [← zpow_add₀ (div_ne_zero hz hn)]
  congr 1
  ring

lemma metaplecticPrefactor_normalization {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) (ℓ : ℤ) :
    gauss r*theta ℓ r*metaplecticRawPrefactor r ℓ = metaplecticPrefactor r ℓ := by
  unfold metaplecticRawPrefactor metaplecticPrefactor
  calc
    _ = (gauss r*star ((Real.sqrt (norm r):ℂ)*gauss r))/
        ((3^(7/2:ℝ)*(2*Real.pi)^2:ℝ):ℂ)*
        (theta ℓ r*((star (r:ℂ)/(r:ℂ))^(-ℓ))) := by ring
    _ = _ := by
      rw [gauss_mul_conj_unnormalized hr hs,angular_conjugate_ratio (primary_ne_zero hr)]
      push_cast
      rfl

lemma norm_metaplecticPrefactor {r : Eisenstein} (hr : r ≠ 0) (ℓ : ℤ) :
    ‖metaplecticPrefactor r ℓ‖ =
      Real.sqrt (norm r)/(3^(7/2:ℝ)*(2*Real.pi)^2) := by
  rw [metaplecticPrefactor,norm_mul,norm_theta hr,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg]
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTransformBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the literal angular Voronoi transform. Its Gamma quotient
is a product of two ordinary shifted Hecke quotients, so the only
special-function input is the same precise DLMF bounded-strip estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticAngularShift_nonneg (ℓ : ℤ) : 0 ≤ metaplecticAngularShift ℓ := by
  unfold metaplecticAngularShift
  positivity

lemma metaplecticGammaQuotient_factor (ℓ : ℤ) (s : ℂ) :
    metaplecticGammaQuotient ℓ s =
      angularGammaFEQuotient (metaplecticAngularShift ℓ) (s+1/6)*
      angularGammaFEQuotient (metaplecticAngularShift ℓ) (s-1/6) := by
  have hk : (metaplecticAngularShift ℓ:ℂ) = (|ℓ|:ℤ)/2 := by
    simp only [metaplecticAngularShift,Complex.ofReal_div,Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
  have h1 : 1-(s+1/6)+(metaplecticAngularShift ℓ:ℂ) = 5/6+(|ℓ|:ℤ)/2-s := by
    rw [hk]
    ring
  have h2 : 1-(s-1/6)+(metaplecticAngularShift ℓ:ℂ) = 7/6+(|ℓ|:ℤ)/2-s := by
    rw [hk]
    ring
  have h3 : s+1/6+(metaplecticAngularShift ℓ:ℂ) = s+(|ℓ|:ℤ)/2+1/6 := by
    rw [hk]
    ring
  have h4 : s-1/6+(metaplecticAngularShift ℓ:ℂ) = s+(|ℓ|:ℤ)/2-1/6 := by
    rw [hk]
    ring
  unfold metaplecticGammaQuotient angularGammaFEQuotient
  rw [h1,h2,h3,h4]
  ring

theorem metaplecticGamma_vertical_bound (ℓ : ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hGamma : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6)) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      ‖metaplecticGammaQuotient ℓ ((-σ:ℝ)+(t:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
  obtain ⟨C,N,hC,hG⟩ := hGamma
  refine ⟨C^2,2*N,by positivity,?_⟩
  intro t
  have hplus : (-σ:ℂ)+(t:ℂ)*Complex.I+1/6 =
      ((-σ+1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by push_cast; ring
  have hminus : (-σ:ℂ)+(t:ℂ)*Complex.I-1/6 =
      ((-σ-1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by push_cast; ring
  rw [metaplecticGammaQuotient_factor]
  simp only [Complex.ofReal_neg]
  rw [hplus,hminus,norm_mul]
  have hp := hG (-σ+1/6) ⟨by linarith,by linarith⟩ t
  have hm := hG (-σ-1/6) ⟨le_rfl,by linarith⟩ t
  calc
    _ ≤ (C*(1+|t|)^N)*(C*(1+|t|)^N) := mul_le_mul hp hm (_root_.norm_nonneg _) (by positivity)
    _ = _ := by rw [two_mul,pow_add]; ring

/-- A uniform weighted Mellin bound gives a uniform transform bound.
This form permits the actual common-support smooth weight families. -/
lemma metaplecticTransform_bound_of_majorant (ℓ : ℤ) (W : ℝ → ℂ) {σ C B : ℝ}
    (hC : 0 ≤ C) (_hB : 0 ≤ B) (N : ℕ)
    (hQ : ∀ t : ℝ, ‖metaplecticGammaQuotient ℓ ((-σ:ℝ)+(t:ℂ)*Complex.I)‖ ≤
      C*(1+|t|)^N)
    (hW : ∀ t : ℝ, ‖mellin W ((-σ:ℝ)+(t:ℂ)*Complex.I)‖*(1+|t|)^N ≤
      mellinEdgeMajorant B t) {v : ℝ} (hv : 0 < v) :
    ‖metaplecticTransform ℓ W σ v‖ ≤
      (‖((1/(2*Real.pi):ℝ):ℂ)‖*C*B*(∫ t : ℝ, mellinEdgeMajorant 1 t))*v^(-σ) := by
  have hI : 0 ≤ ∫ t : ℝ, mellinEdgeMajorant 1 t := integral_nonneg (fun t => by
    unfold mellinEdgeMajorant
    positivity)
  have hb (t : ℝ) :
      ‖(v:ℂ)^(((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)*
        mellin W (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (v^(-σ)*C*B)*mellinEdgeMajorant 1 t := by
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    have hre : (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I).re = -σ := by simp
    rw [hre]
    calc
      _ ≤ (v^(-σ)*(C*(1+|t|)^N))*‖mellin W ((-σ:ℝ)+(t:ℂ)*Complex.I)‖ := by
        gcongr
        exact hQ t
      _ = (v^(-σ)*C)*(‖mellin W ((-σ:ℝ)+(t:ℂ)*Complex.I)‖*(1+|t|)^N) := by ring
      _ ≤ (v^(-σ)*C)*mellinEdgeMajorant B t :=
        mul_le_mul_of_nonneg_left (hW t) (by positivity)
      _ = _ := by unfold mellinEdgeMajorant; ring
  rw [metaplecticTransform,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)‖*
        (∫ t : ℝ, (v^(-σ)*C*B)*mellinEdgeMajorant 1 t) := by
      apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      exact norm_integral_le_of_norm_le ((mellinEdgeMajorant_integrable 1).const_mul _)
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul]; ring

/-- Uniformity in a genuine smooth family follows from its fixed log
support and derivative bounds. -/
theorem UniformLogWeights.metaplecticTransform_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (hW : UniformLogWeights W) (ℓ : ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hGamma : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i v, 0 < v →
      ‖metaplecticTransform ℓ (W i) σ v‖ ≤ C*v^(-σ) := by
  obtain ⟨C,N,hC,hQ⟩ := metaplecticGamma_vertical_bound ℓ hσ hGamma
  obtain ⟨B,hB,hM⟩ := hW.mellin_decay σ (N+2)
  have hI : 0 ≤ ∫ t : ℝ, mellinEdgeMajorant 1 t := integral_nonneg (fun t => by
    unfold mellinEdgeMajorant
    positivity)
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)‖*C*B*(∫ t : ℝ, mellinEdgeMajorant 1 t),by positivity,?_⟩
  intro i v hv
  apply metaplecticTransform_bound_of_majorant ℓ (W i) hC hB.le N hQ _ hv
  intro t
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|t|)^2)).mpr
  calc
    _ = (1+|t|)^(N+2)*‖mellin (W i) ((-σ:ℝ)+(t:ℂ)*Complex.I)‖ := by
      rw [pow_add]
      ring
    _ ≤ B := hM i (-σ) (by simpa only [abs_neg,abs_of_pos hσ] using (le_rfl : σ ≤ σ)) t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic bounds for the actual dual coefficients. Clearing the
ramified denominator identifies every common level prime among the two
supported factors; the free factor is coprime to the level. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_numerator_of_frequency (n : MetaplecticDualArgument)
    {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ) (h h' w : Eisenstein)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3) :
    n.val = lambdaE^(j+1).toNat*ζ.val*h*w*h'^3 := by
  apply Subtype.ext
  have hz : ((j+1).toNat:ℤ) = j+1 := Int.toNat_of_nonneg (by omega)
  have hn : (n.val:ℂ) = metaplecticFrequency n*traceLambda := by
    rw [metaplecticFrequency,div_mul_cancel₀ _ traceLambda_ne_zero]
  rw [hn,he]
  push_cast
  rw [lambdaE_coe,←zpow_natCast traceLambda (j+1).toNat, hz]
  rw [zpow_add₀ traceLambda_ne_zero,zpow_one]
  ring

lemma metaplecticCommonNorm_le_supported {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (k : ℕ) (ζ : Eisensteinˣ)
    {h h' w : Eisenstein} (hh : primary h) (hh' : primary h') (hwr : IsCoprime w r)
    (he : n.val = lambdaE^k*ζ.val*h*w*h'^3) :
    metaplecticCommonNorm r n ≤ norm h*norm h' := by
  let S := (primaryPrimeFactors r).filter (fun p => p ∣ n.val)
  have hsub : S ⊆ primaryPrimeFactors r := Finset.filter_subset _ _
  have hp (p : Eisenstein) (hpm : p ∈ S) : p ∣ h*h' := by
    obtain ⟨hpr,hpn⟩ := Finset.mem_filter.mp hpm
    have hspec := primaryPrimeFactor_spec hr hpr
    have hprime := hspec.1.2
    rw [he] at hpn
    rcases hprime.dvd_mul.mp hpn with hpn | hp'
    · rcases hprime.dvd_mul.mp hpn with hpn | hpw
      · rcases hprime.dvd_mul.mp hpn with hpn | hph
        · rcases hprime.dvd_mul.mp hpn with hpl | hpζ
          · exact False.elim (hprime.not_isUnit
              ((primary_coprime_lambda hr).isUnit_of_dvd' hspec.2
                (hprime.dvd_of_dvd_pow hpl)))
          · exact False.elim (hprime.not_isUnit (isUnit_of_dvd_unit hpζ ζ.isUnit))
        · exact dvd_mul_of_dvd_left hph h'
      · exact False.elim (hprime.not_isUnit (hwr.isUnit_of_dvd' hpw hspec.2))
    · exact dvd_mul_of_dvd_right (hprime.dvd_of_dvd_pow hp') h
  have hdiv := (primary_subsets_prod_dvd hr hsub (h*h')).mpr hp
  have heq : metaplecticCommonNorm r n = norm (∏ p ∈ S, p) := by
    rw [norm_finset_prod]
    rfl
  rw [heq,←norm_mul_eq]
  exact norm_le_of_dvd (mul_ne_zero (primary_ne_zero hh) (primary_ne_zero hh')) hdiv

/-- The published coefficient support gives this bound with no angular
restriction. It will be summed using the actual lattice norm series. -/
lemma metaplectic_actual_coefficient_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (n : MetaplecticDualArgument)
    {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ) {h h' w : Eisenstein}
    (hh : primary h) (hh' : primary h') (hwr : IsCoprime w r)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3)
    (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) :
    ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*(norm h*norm h') := by
  rw [norm_mul]
  apply mul_le_mul ha
    ((norm_metaplecticLocalCoefficient_le hr n).trans
      (metaplecticCommonNorm_le_supported hr n (j+1).toNat ζ hh hh' hwr
        (metaplectic_numerator_of_frequency n hj ζ h h' w he)))
    (_root_.norm_nonneg _) (by positivity)

private lemma metaplectic_norm_pow (a : Eisenstein) (k : ℕ) : norm (a^k) = norm a^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

private lemma metaplectic_lambda_norm : norm lambdaE = 3 := by
  have hs : norm lambdaE^2 = 9 := by
    rw [←metaplectic_norm_pow,lambdaE_sq]
    change Complex.normSq (-3 : ℂ) = 9
    norm_num
  nlinarith [norm_nonneg lambdaE]

lemma metaplectic_frequency_norm (n : MetaplecticDualArgument) (k : ℕ)
    (ζ : Eisensteinˣ) (h h' w : Eisenstein)
    (he : n.val = lambdaE^k*ζ.val*h*w*h'^3) :
    Complex.normSq (metaplecticFrequency n) =
      (3:ℝ)^((k:ℝ)-1)*norm h*norm w*norm h'^3 := by
  have hLambda : Complex.normSq traceLambda = 3 := by
    rw [←lambdaE_coe]
    exact metaplectic_lambda_norm
  rw [metaplecticFrequency,Complex.normSq_div,hLambda]
  change norm n.val/3 = _
  rw [he,norm_mul_eq,norm_mul_eq,norm_mul_eq,norm_mul_eq,
    metaplectic_norm_pow,metaplectic_norm_pow,metaplectic_lambda_norm,
    norm_of_isUnit ζ.isUnit,mul_one]
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<3),Real.rpow_natCast,Real.rpow_one]
  ring

lemma metaplectic_squarefree_supported_divisor {r h : Eisenstein}
    (hh : Squarefree h) (hs : ∃ k : ℕ, h ∣ r^k) : h ∣ r := by
  obtain ⟨k,hk⟩ := hs
  by_cases hk0 : k = 0
  · subst k
    simpa only [pow_zero] using hk.trans (one_dvd r)
  · exact (hh.dvd_pow_iff_dvd hk0).mp hk

lemma metaplectic_supported_divisor_mem {r h w : Eisenstein}
    (hr : primary r) (hh : primary h) (hs : Squarefree (h*w))
    (hdiv : ∃ k : ℕ, h ∣ r^k) : h ∈ metaplecticPrimaryDivisors r := by
  have hhdiv : h ∣ r := metaplectic_squarefree_supported_divisor (hs.squarefree_of_dvd (dvd_mul_right h w)) hdiv
  exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
    ⟨hh,norm_le_of_dvd (primary_ne_zero hr) hhdiv⟩,hhdiv⟩

lemma metaplectic_units_finite : Finite (Eisensteinˣ) := by
  let f : Eisensteinˣ → {u : Eisenstein // u ∈ nonzeroNormBall 1} := fun u =>
    ⟨u,mem_nonzeroNormBall.mpr ⟨by rw [norm_of_isUnit u.isUnit],u.ne_zero⟩⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Units.ext
    exact congrArg Subtype.val h
  exact Finite.of_injective f hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dual coefficient bound becomes a product of a geometric
ramified factor and convergent norm powers. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_monomial_decay {H P W : ℝ} (hH : 0 < H) (hP : 0 < P) (hW : 0 < W)
    (σ : ℝ) (k : ℕ) :
    ((3:ℝ)^((k:ℝ)/3)*Real.sqrt P*(H*P))/
        (((3:ℝ)^((k:ℝ)-1)*H*W*P^3)^(1+σ)) =
      (3:ℝ)^(1+σ)*metaplecticRamifiedRatio σ^k*
        H^(-σ)*W^(-1-σ)*P^(-3/2-3*σ) := by
  have h3 : (3:ℝ)^((k:ℝ)/3)/(((3:ℝ)^((k:ℝ)-1))^(1+σ)) =
      (3:ℝ)^(1+σ)*metaplecticRamifiedRatio σ^k := by
    rw [←Real.rpow_mul (by norm_num),←Real.rpow_sub (by norm_num)]
    unfold metaplecticRamifiedRatio
    rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hH' : H/H^(1+σ) = H^(-σ) := by
    calc
      _ = H^(1:ℝ)/H^(1+σ) := by rw [Real.rpow_one]
      _ = H^(1-(1+σ)) := (Real.rpow_sub hH _ _).symm
      _ = _ := by congr 1; ring
  have hW' : 1/W^(1+σ) = W^(-1-σ) := by
    rw [one_div,←Real.rpow_neg hW.le]
    congr 1
    ring
  have hP' : (Real.sqrt P*P)/(P^3)^(1+σ) = P^(-3/2-3*σ) := by
    calc
      _ = (P^(1/2:ℝ)*P^(1:ℝ))/P^((3:ℝ)*(1+σ)) := by
        rw [Real.sqrt_eq_rpow,Real.rpow_one,←Real.rpow_natCast_mul hP.le]
        norm_num
      _ = P^((1/2+1)-(3:ℝ)*(1+σ)) := by
        rw [←Real.rpow_add hP,←Real.rpow_sub hP]
      _ = _ := by congr 1; ring
  rw [Real.mul_rpow (by positivity) (pow_nonneg hP.le _),
    Real.mul_rpow (by positivity) hW.le,
    Real.mul_rpow (by positivity) hH.le]
  calc
    _ = ((3:ℝ)^((k:ℝ)/3)/(((3:ℝ)^((k:ℝ)-1))^(1+σ)))*
        (H/H^(1+σ))*(1/W^(1+σ))*((Real.sqrt P*P)/(P^3)^(1+σ)) := by ring
    _ = _ := by rw [h3,hH',hW',hP']

lemma metaplecticRamifiedRatio_bounds {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ metaplecticRamifiedRatio σ ∧ metaplecticRamifiedRatio σ < 1 := by
  exact ⟨Real.rpow_nonneg (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

/-- Decay of an actual nonzero Voronoi coefficient with its published
support representation. The free and cubed factors now have convergent
norm exponents. -/
theorem metaplectic_coefficient_decay
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (n : MetaplecticDualArgument)
    {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ) {h h' w : Eisenstein}
    (hh : primary h) (hh' : primary h') (hw : primary w) (hwr : IsCoprime w r)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3)
    (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) (σ : ℝ) :
    ‖a r n*metaplecticLocalCoefficient r n‖/
        (Complex.normSq (metaplecticFrequency n))^(1+σ) ≤
      C*(3:ℝ)^(1+σ)*metaplecticRamifiedRatio σ^((j+1).toNat)*
        norm h^(-σ)*norm w^(-1-σ)*norm h'^(-3/2-3*σ) := by
  let k := (j+1).toNat
  have hjk : (k:ℝ) = (j:ℝ)+1 := by
    dsimp [k]
    have hi : (((j+1).toNat:ℕ):ℤ) = j+1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hi
  have hmax : ((max j 0:ℤ):ℝ) ≤ k := by
    rw [hjk]
    exact_mod_cast (show max j 0 ≤ j+1 by omega)
  have h3 : (3:ℝ)^((max j 0:ℤ)/3:ℝ) ≤ (3:ℝ)^((k:ℝ)/3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hh0 := norm_nonneg h
  have hhp0 := norm_nonneg h'
  have hw0 := norm_nonneg w
  have hc := metaplectic_actual_coefficient_bound hC hr n hj ζ hh hh' hwr he ha
  have hc' : ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*((3:ℝ)^((k:ℝ)/3)*Real.sqrt (norm h')*(norm h*norm h')) := by
    calc
      _ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*(norm h*norm h') := hc
      _ ≤ C*3^((k:ℝ)/3)*Real.sqrt (norm h')*(norm h*norm h') := by gcongr
      _ = _ := by ring
  have hn := metaplectic_frequency_norm n k ζ h h' w
    (metaplectic_numerator_of_frequency n hj ζ h h' w he)
  rw [hn]
  apply (div_le_div_of_nonneg_right hc' (by positivity)).trans_eq
  rw [mul_div_assoc,metaplectic_monomial_decay
    (norm_pos_of_ne_zero (primary_ne_zero hh))
    (norm_pos_of_ne_zero (primary_ne_zero hh'))
    (norm_pos_of_ne_zero (primary_ne_zero hw)) σ k]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the separated arithmetic majorant from the actual Voronoi
support. The two free norm series and the ramified geometric series
converge, while the squarefree supported factor is a divisor of the level. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_divisor_weight_small_power {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ)) ≤ C*norm r^ε := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro r hr
  calc
    _ ≤ ∑ _h ∈ metaplecticPrimaryDivisors r, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (one_le_norm (primary_ne_zero (mem_primaryElementBall.mp (Finset.mem_filter.mp hh).1).1))
        (by linarith)
    _ = ((metaplecticPrimaryDivisors r).card:ℝ) := by simp
    _ ≤ C*norm r^ε := hdiv (primaryElementBall (norm r))
      (fun _ hh => (mem_primaryElementBall.mp hh).1) r (primary_ne_zero hr)

lemma metaplecticCodeWeight_nonneg (r : Eisenstein) (σ : ℝ)
    (z : MetaplecticCoefficientCode r) : 0 ≤ metaplecticCodeWeight r σ z := by
  unfold metaplecticCodeWeight metaplecticRamifiedRatio
  exact mul_nonneg (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
    (mul_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))))

private lemma metaplectic_product_hasSum {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    {A B : ℝ} (hf : HasSum f A) (hg : HasSum g B)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b) :
    HasSum (fun z : α × β => f z.1*g z.2) (A*B) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable hf0 hg0)

lemma metaplecticCodeWeight_hasSum (r : Eisenstein) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (metaplecticCodeWeight r σ)
      ((1-metaplecticRamifiedRatio σ)⁻¹*(Nat.card (Eisensteinˣ):ℝ)*
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ))*
      (∑' h : PrimaryArgument, norm h^(-3/2-3*σ))*
      (∑' w : PrimaryArgument, norm w^(-1-σ))) := by
  let : Finite (Eisensteinˣ) := metaplectic_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  have hq := metaplecticRamifiedRatio_bounds hσ
  have hk := hasSum_geometric_of_lt_one hq.1 hq.2
  have hw : Summable (fun w : PrimaryArgument => norm w^(-1-σ)) := by
    convert primary_norm_rpow_summable (show 1 < 1+σ by linarith) using 1
    all_goals try with_reducible_and_instances rfl
    ext w
    congr 1
    ring
  have hp : Summable (fun h : PrimaryArgument => norm h^(-3/2-3*σ)) := by
    convert primary_norm_rpow_summable (show 1 < 3/2+3*σ by linarith) using 1
    all_goals try with_reducible_and_instances rfl
    ext w
    congr 1
    ring
  have hpw := metaplectic_product_hasSum hp.hasSum hw.hasSum
    (fun h => Real.rpow_nonneg (norm_nonneg h) _)
    (fun w => Real.rpow_nonneg (norm_nonneg w) _)
  have hh : HasSum (fun h : metaplecticPrimaryDivisors r => norm h.val^(-σ))
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ)) := by
    rw [←Finset.sum_coe_sort]
    exact hasSum_fintype _
  have hhpw := metaplectic_product_hasSum hh hpw
    (fun h => Real.rpow_nonneg (norm_nonneg h.val) _)
    (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg z.1) _)
      (Real.rpow_nonneg (norm_nonneg z.2) _))
  have hu : HasSum (fun _ : Eisensteinˣ => (1:ℝ)) (Nat.card (Eisensteinˣ):ℝ) := by
    simpa using (hasSum_fintype (fun _ : Eisensteinˣ => (1:ℝ)))
  have huh := metaplectic_product_hasSum hu hhpw (fun _ => zero_le_one)
    (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg z.1.val) _)
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg z.2.1) _)
        (Real.rpow_nonneg (norm_nonneg z.2.2) _)))
  have hall := metaplectic_product_hasSum hk huh (fun _ => pow_nonneg hq.1 _)
    (fun z => mul_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (norm_nonneg z.2.1.val) _)
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg z.2.2.1) _)
        (Real.rpow_nonneg (norm_nonneg z.2.2.2) _))))
  change HasSum (fun z : MetaplecticCoefficientCode r => metaplecticCodeWeight r σ z) _
  simpa only [metaplecticCodeWeight,mul_assoc] using hall

lemma metaplecticCodeWeight_summable (r : Eisenstein) {σ : ℝ} (hσ : 0 < σ) :
    Summable (metaplecticCodeWeight r σ) := (metaplecticCodeWeight_hasSum r hσ).summable

lemma metaplecticCodeWeight_tsum (r : Eisenstein) {σ : ℝ} (hσ : 0 < σ) :
    (∑' z : MetaplecticCoefficientCode r, metaplecticCodeWeight r σ z) =
      (1-metaplecticRamifiedRatio σ)⁻¹*(Nat.card (Eisensteinˣ):ℝ)*
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ))*
      (∑' h : PrimaryArgument, norm h^(-3/2-3*σ))*
      (∑' w : PrimaryArgument, norm w^(-1-σ)) :=
  (metaplecticCodeWeight_hasSum r hσ).tsum_eq

/-- The full separated majorant has an arbitrarily small level loss. -/
theorem metaplecticCodeWeight_small_power {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      (∑' z : MetaplecticCoefficientCode r, metaplecticCodeWeight r σ z) ≤ C*norm r^ε := by
  obtain ⟨D,hD,hdiv⟩ := metaplectic_divisor_weight_small_power hε hσ
  let A := (1-metaplecticRamifiedRatio σ)⁻¹*(Nat.card (Eisensteinˣ):ℝ)*
    (∑' h : PrimaryArgument, norm h^(-3/2-3*σ))*
    (∑' w : PrimaryArgument, norm w^(-1-σ))
  have hA : 0 ≤ A := by
    have hden : 0 ≤ 1-metaplecticRamifiedRatio σ :=
      sub_nonneg.mpr (metaplecticRamifiedRatio_bounds hσ).2.le
    have hp : 0 ≤ ∑' h : PrimaryArgument, norm h^(-3/2-3*σ) :=
      tsum_nonneg (fun h => Real.rpow_nonneg (norm_nonneg h) _)
    have hw : 0 ≤ ∑' w : PrimaryArgument, norm w^(-1-σ) :=
      tsum_nonneg (fun w => Real.rpow_nonneg (norm_nonneg w) _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hden) (Nat.cast_nonneg _)) hp) hw
  refine ⟨D*(A+1),mul_pos hD (by linarith),?_⟩
  intro r hr
  rw [metaplecticCodeWeight_tsum r hσ]
  calc
    _ = A*(∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ)) := by dsimp [A]; ring
    _ ≤ A*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hdiv r hr) hA
    _ ≤ D*(A+1)*norm r^ε := by nlinarith [Real.rpow_nonneg (norm_nonneg r) ε]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injective coding of the actual published theta coefficients gives
the absolute dual coefficient mass with a subpower level loss. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticCoefficientMassTerm_nonneg
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (σ : ℝ)
    (n : MetaplecticDualArgument) : 0 ≤ metaplecticCoefficientMassTerm a r σ n := by
  exact div_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg _) _)

lemma metaplectic_coefficient_codes
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    (σ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ n : MetaplecticDualArgument, a r n*metaplecticLocalCoefficient r n ≠ 0 →
        ∃ z : MetaplecticCoefficientCode r,
          n.val = metaplecticDecode r z ∧
          metaplecticCoefficientMassTerm a r σ n ≤ K*metaplecticCodeWeight r σ z := by
  obtain ⟨C,hC,hbound⟩ := ha
  refine ⟨C*(3:ℝ)^(1+σ),mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  intro r hr hsr n hn
  obtain ⟨j,ζ,h,h',w,hj,hh,hh',hw,hdiv,_h'div,hwr,hs,he,hcoef⟩ := hbound r hr hsr n hn
  let z : MetaplecticCoefficientCode r :=
    ((j+1).toNat,ζ,⟨h,metaplectic_supported_divisor_mem hr hh hs hdiv⟩,⟨h',hh'⟩,⟨w,hw⟩)
  refine ⟨z,metaplectic_numerator_of_frequency n hj ζ h h' w he,?_⟩
  have hb := metaplectic_coefficient_decay hC.le hr n hj ζ hh hh' hw hwr he hcoef σ
  apply hb.trans_eq
  dsimp [metaplecticCodeWeight,z]
  ring

/-- The absolute dual coefficient sum is derived from the literal
published support formula, not postulated as a Voronoi estimate. -/
theorem metaplectic_coefficient_mass_small_power
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      Summable (metaplecticCoefficientMassTerm a r σ) ∧
      (∑' n : MetaplecticDualArgument, metaplecticCoefficientMassTerm a r σ n) ≤ C*norm r^ε := by
  obtain ⟨K,hK,hcodes⟩ := metaplectic_coefficient_codes ha σ
  obtain ⟨D,hD,hcodeBound⟩ := metaplecticCodeWeight_small_power hε hσ
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro r hr hsr
  let I := {n : MetaplecticDualArgument // a r n*metaplecticLocalCoefficient r n ≠ 0}
  choose f he hb using fun n : I => hcodes r hr hsr n.val n.property
  have hf : Function.Injective f := by
    intro n m hfm
    apply Subtype.ext
    apply Subtype.ext
    exact (he n).trans ((congrArg (metaplecticDecode r) hfm).trans (he m).symm)
  have hfullCode : Summable (fun z : MetaplecticCoefficientCode r => K*metaplecticCodeWeight r σ z) :=
    (metaplecticCodeWeight_summable r hσ).mul_left K
  have hI : Summable (fun n : I => metaplecticCoefficientMassTerm a r σ n) :=
    (hfullCode.comp_injective hf).of_nonneg_of_le
      (fun n => metaplecticCoefficientMassTerm_nonneg a r σ n) hb
  have hsupp : Function.support (metaplecticCoefficientMassTerm a r σ) ⊆
      {n | a r n*metaplecticLocalCoefficient r n ≠ 0} := by
    intro n hn hezero
    exact hn (by simp [metaplecticCoefficientMassTerm,hezero])
  have hsum : HasSum (metaplecticCoefficientMassTerm a r σ)
      (∑' n : I, metaplecticCoefficientMassTerm a r σ n) :=
    (hasSum_subtype_iff_of_support_subset hsupp).mp hI.hasSum
  refine ⟨hsum.summable,?_⟩
  rw [hsum.tsum_eq]
  calc
    _ ≤ ∑' z : MetaplecticCoefficientCode r, K*metaplecticCodeWeight r σ z :=
      hI.tsum_le_tsum_of_inj f hf
        (fun z _ => mul_nonneg hK.le (metaplecticCodeWeight_nonneg r σ z)) hb hfullCode
    _ = K*(∑' z : MetaplecticCoefficientCode r, metaplecticCodeWeight r σ z) :=
      (metaplecticCodeWeight_summable r hσ).tsum_mul_left K
    _ ≤ K*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hcodeBound r hr) hK.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticDualScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scaling of the actual angular Voronoi terms. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_complexAngular {z : ℂ} (hz : z ≠ 0) (ℓ : ℤ) : ‖complexAngular ℓ z‖ = 1 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp [complexAngular,norm_zpow,hn]

lemma metaplectic_argument_power {B D P R X : ℝ}
    (hB : 0 < B) (hD : 0 < D) (hP : 0 < P) (hR : 0 < R) (hX : 0 < X) (σ : ℝ) :
    ((B^4*D^3*P*X)/R^2)^(-σ) =
      B^(-4*σ)*D^(-3*σ)*P^(-σ)*X^(-σ)*R^(2*σ) := by
  have hb : (B^4)^(-σ) = B^(-4*σ) := by
    rw [←Real.rpow_natCast_mul hB.le]
    congr 1
    norm_num
  have hd : (D^3)^(-σ) = D^(-3*σ) := by
    rw [←Real.rpow_natCast_mul hD.le]
    congr 1
    norm_num
  have hr : (R^2)^(-σ) = (R^(2*σ))⁻¹ := by
    rw [←Real.rpow_natCast_mul hR.le,←Real.rpow_neg hR.le]
    congr 1
    norm_num
  rw [Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hX.le,
    Real.mul_rpow (by positivity) hP.le,
    Real.mul_rpow (by positivity) (pow_nonneg hD.le _),hb,hd,hr,
    div_eq_mul_inv,inv_inv]

lemma metaplectic_dual_scalar {A B D P R X : ℝ}
    (hB : 0 < B) (hD : 0 < D) (hP : 0 < P) (hR : 0 < R) (hX : 0 < X) (σ : ℝ) :
    A/(P*D^(5/2:ℝ))*((B^4*D^3*P*X)/R^2)^(-σ) =
      (B^(-4*σ)*X^(-σ)*R^(2*σ))*(A/P^(1+σ))*D^(-5/2-3*σ) := by
  have hp : P^(-σ)/P = (P^(1+σ))⁻¹ := by
    calc
      _ = P^(-σ)/P^(1:ℝ) := by rw [Real.rpow_one]
      _ = P^(-σ-1) := (Real.rpow_sub hP _ _).symm
      _ = P^(-(1+σ)) := by congr 1; ring
      _ = _ := Real.rpow_neg hP.le _
  have hd : D^(-3*σ)/D^(5/2:ℝ) = D^(-5/2-3*σ) := by
    rw [←Real.rpow_sub hD]
    congr 1
    ring
  rw [metaplectic_argument_power hB hD hP hR hX]
  calc
    _ = (B^(-4*σ)*X^(-σ)*R^(2*σ))*A*(P^(-σ)/P)*(D^(-3*σ)/D^(5/2:ℝ)) := by ring
    _ = _ := by rw [hp,hd]; ring

/-- The actual dual term has the separated coefficient/d-variable
majorant supplied by the published formula and the derived transform bound. -/
lemma metaplecticDualTerm_norm_le
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) {σ X C : ℝ} (hX : 0 < X) (hC : 0 ≤ C)
    (hW : ∀ v : ℝ, 0 < v → ‖metaplecticTransform ℓ W σ v‖ ≤ C*v^(-σ))
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    ‖metaplecticDualTerm a r ℓ W σ X nd‖ ≤
      (C*((2*Real.pi)^(-4*σ)*X^(-σ)*norm r^(2*σ)))*
        metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ) := by
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hD : 0 < norm nd.2 := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hP : 0 < Complex.normSq (metaplecticFrequency nd.1) :=
    Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1)
  have hB : 0 < 2*Real.pi := by positivity
  have hz : ((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (fun h => primary_ne_zero nd.2.property (Subtype.ext h)))
      (metaplecticFrequency_ne_zero nd.1)
  have hnorm : Complex.normSq (((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1) =
      norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1) := by
    rw [Complex.normSq_mul,map_pow]
    rfl
  unfold metaplecticDualTerm
  split_ifs
  · rw [norm_mul,norm_mul,norm_div,Complex.norm_real,
      Real.norm_of_nonneg (by positivity),norm_complexAngular hz,mul_one,hnorm]
    have hv : 0 < (2*Real.pi)^4*(norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1))*X/norm r^2 := by
      positivity
    apply (mul_le_mul_of_nonneg_left (hW _ hv) (by positivity)).trans_eq
    rw [mul_left_comm _ C,mul_assoc]
    have hs := metaplectic_dual_scalar (A := ‖a r nd.1*metaplecticLocalCoefficient r nd.1‖)
      hB hD hP hR hX σ
    change C*(_/(_*_) * _^(-σ)) = _
    rw [show (2*Real.pi)^4*(norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)*X)/norm r^2 =
      ((2*Real.pi)^4*norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)*X)/norm r^2 by ring,hs]
    unfold metaplecticCoefficientMassTerm
    ring
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity))
      (metaplecticCoefficientMassTerm_nonneg a r σ nd.1)) (Real.rpow_nonneg hD.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletedLow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-height completed angular estimate, derived from the actual
published Voronoi identity, coefficient support, and Gamma strip bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

private lemma norm_tsum_le_separated {α β : Type*}
    (f : α × β → ℂ) (u : α → ℝ) (v : β → ℝ) {K M : ℝ}
    (hu : Summable u) (hv : Summable v)
    (hu0 : ∀ a, 0 ≤ u a) (hv0 : ∀ b, 0 ≤ v b) (hK : 0 ≤ K)
    (hM : (∑' a, u a) ≤ M)
    (hpoint : ∀ z, ‖f z‖ ≤ K*(u z.1*v z.2)) :
    ‖∑' z, f z‖ ≤ K*M*(∑' b, v b) := by
  have hp : Summable (fun z : α × β => u z.1*v z.2) :=
    hu.mul_of_nonneg hv hu0 hv0
  have hs : HasSum (fun z : α × β => K*(u z.1*v z.2))
      (K*((∑' a, u a)*(∑' b, v b))) :=
    (hu.hasSum.mul hv.hasSum hp).mul_left K
  have hb : ‖∑' z, f z‖ ≤ K*((∑' a, u a)*(∑' b, v b)) :=
    tsum_of_norm_bounded hs hpoint
  calc
    _ ≤ K*((∑' a, u a)*(∑' b, v b)) := hb
    _ ≤ K*(M*(∑' b, v b)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hM (tsum_nonneg hv0)) hK
    _ = _ := by ring

private lemma metaplectic_d_weight_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun d : PrimaryArgument => norm d^(-5/2-3*σ)) := by
  convert primary_norm_rpow_summable (show 1 < 5/2+3*σ by linarith) using 1
  all_goals try with_reducible_and_instances rfl
  ext d
  congr 1
  ring

lemma metaplecticDualTerm_tsum_norm_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {r : Eisenstein}
    (hr : primary r) (ℓ : ℤ) (W : ℝ → ℂ) {σ X C M : ℝ}
    (hσ : 0 < σ) (hX : 0 < X) (hC : 0 ≤ C)
    (hW : ∀ v : ℝ, 0 < v → ‖metaplecticTransform ℓ W σ v‖ ≤ C*v^(-σ))
    (hm : Summable (metaplecticCoefficientMassTerm a r σ))
    (hM : (∑' n, metaplecticCoefficientMassTerm a r σ n) ≤ M) :
    ‖∑' nd : MetaplecticDualArgument × PrimaryArgument, metaplecticDualTerm a r ℓ W σ X nd‖ ≤
      (C*((2*Real.pi)^(-4*σ)*X^(-σ)*norm r^(2*σ)))*M*
        (∑' d : PrimaryArgument, norm d^(-5/2-3*σ)) := by
  apply norm_tsum_le_separated _ (metaplecticCoefficientMassTerm a r σ)
    (fun d : PrimaryArgument => norm d^(-5/2-3*σ)) hm
    (metaplectic_d_weight_summable hσ) (metaplecticCoefficientMassTerm_nonneg a r σ)
    (fun d => Real.rpow_nonneg (norm_nonneg d) _)
    (mul_nonneg hC (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg hX.le _)) (Real.rpow_nonneg (norm_nonneg r) _))) hM
  intro nd
  simpa only [mul_assoc] using metaplecticDualTerm_norm_le a hr ℓ W hX hC hW nd

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNineCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed first column with lower-right entry divisible by nine.
This makes the common-lattice additive phase a literal residue character. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaNineGaussMatrix_multiplier (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (j : Fin 3) :
    cubicThetaProjectedCuspMultiplier (cubicThetaNineGaussMatrix r hr u hu)
      (cubicThetaNineGaussMatrix_primary r hr u hu) j=cubicSymbol r u := by
  let g := cubicThetaNineGaussMatrix r hr u hu
  have hc := cubicThetaNineGaussMatrix_primary r hr u hu
  have hd : (3:Eisenstein)∣g 1 1 :=
    dvd_trans (show (3:Eisenstein)∣9 from ⟨3,by norm_num⟩) (cubicThetaNineGaussMatrix_nine r hr u hu)
  have ha : (3:Eisenstein)∣g 0 0 := by
    rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1]
    refine ⟨-lambdaE*u,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  rw [cubicThetaProjectedCuspMultiplier_constant g hc hd j,
    cubicThetaPrimaryBottom_multiplier_adapted g hc ha hd,
    (cubicThetaNineGaussMatrix_entries r hr u hu).2.1,
    (cubicThetaNineGaussMatrix_entries r hr u hu).1,
    cubicSymbol_mul_upper hr,cubicSymbol_pow_upper hr,
    cubicSymbol_cube_of_isCoprime hr lambdaE (primary_coprime_lambda hr),one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonCuspCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dual three-cusp coefficient before local cube cancellation.
All dependence on a coprime additive numerator is in its cubic character. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaProjectedCoefficient_factor (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0)
    (hd : (3:Eisenstein)∣g 1 1) (n : Eisenstein) :
    cubicThetaProjectedCoefficient g hc n=
      star (cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc))*
        cubicThetaCommonCuspCoefficient n := by
  have ht (j : Fin 3) : cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j)=
      cubicThetaActualCuspCoefficient (j.val:ℤ) :=
    cubicThetaActualCuspCoefficient_periodic (cubicThetaProjectedCuspType_congr g hc ha j)
  unfold cubicThetaProjectedCoefficient cubicThetaCommonCuspCoefficient
  simp_rw [cubicThetaProjectedCuspMultiplier_constant g hc hd,ht]
  rw [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cubicThetaNineGaussMatrix_coefficient (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (n : Eisenstein) :
    cubicThetaProjectedCoefficient (cubicThetaNineGaussMatrix r hr u hu)
      (cubicThetaNineGaussMatrix_primary r hr u hu) n=
      star (cubicSymbol r u)*cubicThetaCommonCuspCoefficient n := by
  let g := cubicThetaNineGaussMatrix r hr u hu
  have hc := cubicThetaNineGaussMatrix_primary r hr u hu
  have hd : (3:Eisenstein)∣g 1 1 :=
    dvd_trans (show (3:Eisenstein)∣9 from ⟨3,by norm_num⟩) (cubicThetaNineGaussMatrix_nine r hr u hu)
  have ha : (3:Eisenstein)∣g 0 0 := by
    rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1]
    refine ⟨-lambdaE*u,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  rw [cubicThetaProjectedCoefficient_factor g hc ha hd]
  have he := cubicThetaProjectedCuspMultiplier_constant g hc hd (0:Fin 3)
  rw [cubicThetaNineGaussMatrix_multiplier] at he
  rw [←he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing an unramified prime cube preserves the exact arithmetic
support. Consequently cube scaling holds on every index, including the
zero extension of all three coefficient families. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCoordinates_primeCube_dvd {p n : Eisenstein} (hp : primaryPrime p)
    (R : CubicThetaCoordinates (n*p^3)) : p ∣ R.cubePart := by
  by_contra hd
  have hpu : IsCoprime p (R.unit:Eisenstein) := hp.2.coprime_iff_not_dvd.mpr
    (fun hv => hp.2.not_isUnit (isUnit_of_dvd_unit hv R.unit.isUnit))
  have hpl : IsCoprime p (lambdaE^R.order) := (primary_coprime_lambda hp.1).pow_right
  have hpd : IsCoprime p (R.cubePart^3) := (hp.2.coprime_iff_not_dvd.mpr hd).pow_right
  have hc : p^2 ∣ R.squarefreePart := by
    have heq : n*p^3=((R.unit:Eisenstein)*lambdaE^R.order*R.cubePart^3)*R.squarefreePart :=
      R.numerator_eq.trans (by ring)
    have he : p^2 ∣ ((R.unit:Eisenstein)*lambdaE^R.order*R.cubePart^3)*R.squarefreePart :=
      ((pow_dvd_pow p (by omega : 2 ≤ 3)).trans (dvd_mul_left (p^3) n)).trans (dvd_of_eq heq)
    exact ((hpu.mul_right hpl).mul_right hpd).pow_left.dvd_of_dvd_mul_left he
  exact hp.2.not_isUnit (R.squarefree p (by simpa only [pow_two] using hc))

theorem cubicThetaCoordinates_remove_primeCube {p n : Eisenstein} (hp : primaryPrime p)
    (R : CubicThetaCoordinates (n*p^3)) : Nonempty (CubicThetaCoordinates n) := by
  obtain ⟨d,hd⟩ := cubicThetaCoordinates_primeCube_dvd hp R
  have hdp : primary d := primary_of_mul hp.1 (hd ▸ R.cube_primary)
  refine ⟨{
    unit := R.unit
    order := R.order
    squarefreePart := R.squarefreePart
    cubePart := d
    squarefree_primary := R.squarefree_primary
    cube_primary := hdp
    squarefree := R.squarefree
    numerator_eq := ?_ }⟩
  apply mul_right_cancel₀ (pow_ne_zero 3 hp.2.ne_zero)
  calc
    n*p^3 = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
    _ = ((R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*d^3))*p^3 := by rw [hd]; ring

theorem cubicThetaCoordinates_primeCube_iff {p n : Eisenstein} (hp : primaryPrime p) :
    Nonempty (CubicThetaCoordinates (n*p^3)) ↔ Nonempty (CubicThetaCoordinates n) := by
  constructor
  · rintro ⟨R⟩
    exact cubicThetaCoordinates_remove_primeCube hp R
  · rintro ⟨R⟩
    exact ⟨R.mulPrimaryCube p hp.1⟩

theorem cubicThetaArithmeticCoefficient_primeCube {p : Eisenstein} (hp : primaryPrime p)
    (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (n*p^3)=(norm p:ℂ)⁻¹*cubicThetaArithmeticCoefficient n := by
  classical
  by_cases hn : Nonempty (CubicThetaCoordinates n)
  · exact cubicThetaArithmeticCoefficient_mulPrimaryCube (Classical.choice hn) p hp.1
  · have hnp := mt (cubicThetaCoordinates_primeCube_iff hp).mp hn
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hn,dite_eq_right hnp,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonCubeScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing a primary cube scales the actual three-cusp coefficient by
its norm. This includes all zero-extension cases. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicThetaArithmeticCoefficient_primaryCube (d : Eisenstein) (hd : primary d)
    (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaArithmeticCoefficient n := by
  revert n
  apply primary_induction (b:=d) ?_ ?_ hd
  · intro n
    have h1 : norm (1:Eisenstein)=1 := by norm_num [norm]
    simp only [one_pow,mul_one,h1,Complex.ofReal_one,inv_one,one_mul]
  · intro p b hp hb ih n
    rw [show n*(p*b)^3=(n*p^3)*b^3 by ring,ih,
      cubicThetaArithmeticCoefficient_primeCube hp,norm_mul_eq,Complex.ofReal_mul,mul_inv_rev]
    ring

lemma cubicThetaShiftedLatticeCoefficient_primaryCube (j : ℤ) (d : Eisenstein)
    (hd : primary d) (n : Eisenstein) :
    cubicThetaShiftedLatticeCoefficient j (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaShiftedLatticeCoefficient j n := by
  have hp : primary (d^3) := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using primary_mul hd (primary_mul hd hd)
  have hl3 : lambdaE∣(3:Eisenstein) := ⟨-lambdaE,by
    rw [mul_neg,←pow_two,lambdaE_sq,neg_neg]⟩
  have hl : lambdaE∣n*d^3-n := by
    have H := dvd_mul_of_dvd_right (dvd_trans hl3 hp) n
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hi : lambdaE∣n*d^3-(j:Eisenstein) ↔ lambdaE∣n-(j:Eisenstein) := by
    constructor
    · intro h
      convert dvd_sub h hl using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · intro h
      convert dvd_add h hl using 1
      all_goals try with_reducible_and_instances rfl
      ring
  unfold cubicThetaShiftedLatticeCoefficient
  rw [hi]
  split_ifs
  · rw [show 3*(lambdaE*(n*d^3))=(3*(lambdaE*n))*d^3 by ring,
      cubicThetaArithmeticCoefficient_primaryCube d hd]
    ring
  · ring

lemma cubicThetaActualCuspCoefficient_primaryCube (j : ℤ) (d : Eisenstein)
    (hd : primary d) (n : Eisenstein) :
    cubicThetaActualCuspCoefficient j (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaActualCuspCoefficient j n := by
  unfold cubicThetaActualCuspCoefficient
  split_ifs
  · exact cubicThetaArithmeticCoefficient_primaryCube d hd n
  · exact cubicThetaShiftedLatticeCoefficient_primaryCube j d hd n

theorem cubicThetaCommonCuspCoefficient_primaryCube (d : Eisenstein)
    (hd : primary d) (n : Eisenstein) :
    cubicThetaCommonCuspCoefficient (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaCommonCuspCoefficient n := by
  unfold cubicThetaCommonCuspCoefficient
  simp_rw [show -(n*d^3)=(-n)*d^3 by ring,
    cubicThetaActualCuspCoefficient_primaryCube _ d hd,star_mul]
  simp only [map_inv₀,Complex.star_def,Complex.conj_ofReal]
  rw [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual three-cusp coefficient has squarefree-times-cube support.
This is proved for the constructed cusps, including their ramified shifts. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaArithmetic_zero_of_no_primary_coordinates {h : Eisenstein}
    (hh : primary h)
    (hn : ¬∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3)
    (e : Eisensteinˣ) (k : ℕ) :
    cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^k*h)=0 := by
  unfold cubicThetaArithmeticCoefficient
  apply dite_eq_right
  exact fun he => hn ((cubicThetaCoordinates_primary_power_iff hh e k).mp he)

lemma cubicThetaCommon_zero_of_no_primary_coordinates {h : Eisenstein}
    (hh : primary h)
    (hn : ¬∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3)
    (e : Eisensteinˣ) (k : ℕ) :
    cubicThetaCommonCuspCoefficient ((e:Eisenstein)*lambdaE^k*h)=0 := by
  have hbase : cubicThetaArithmeticCoefficient (-((e:Eisenstein)*lambdaE^k*h))=0 := by
    simpa only [Units.val_neg,neg_mul] using
      cubicThetaArithmetic_zero_of_no_primary_coordinates hh hn (-e) k
  have hshift : cubicThetaArithmeticCoefficient
      (3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*h))))=0 := by
    have he : 3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*h)))=
        (e:Eisenstein)*lambdaE^(k+3)*h := by
      rw [pow_add,pow_succ,lambdaE_sq]
      ring
    rw [he]
    exact cubicThetaArithmetic_zero_of_no_primary_coordinates hh hn e (k+3)
  have hc (j : ℤ) :
      cubicThetaActualCuspCoefficient j (-((e:Eisenstein)*lambdaE^k*h))=0 := by
    unfold cubicThetaActualCuspCoefficient
    split_ifs
    · exact hbase
    · simp only [cubicThetaShiftedLatticeCoefficient,hshift,mul_zero,ite_self]
  unfold cubicThetaCommonCuspCoefficient
  simp only [hc,star_zero,mul_zero,Finset.sum_const_zero,zero_div]

theorem cubicThetaCommonCuspCoefficient_support {n : Eisenstein} (hn : n≠0)
    (ha : cubicThetaCommonCuspCoefficient n≠0) : Nonempty (CubicThetaCoordinates n) := by
  obtain ⟨e,k,h,hh,he⟩ := unit_ramified_primary_decomposition hn
  obtain ⟨c,d,hc,hd,hs,hcd⟩ :
      ∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3 := by
    by_contra hbad
    rw [he,cubicThetaCommon_zero_of_no_primary_coordinates hh hbad] at ha
    exact ha rfl
  exact ⟨{
    unit := e
    order := k
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := by rw [he,hcd] }⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dual support is indexed once by its unit, ramified order,
squarefree primary factor and primary cube factor. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCommonNumerator_injective : Function.Injective cubicThetaCommonNumerator := by
  rintro ⟨u,k,cd⟩ ⟨v,l,ef⟩ he
  have hp (x : CubicThetaPrimaryPair) : primary (x.val.1*x.val.2^3) :=
    primary_mul x.property.1 (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul x.property.2.1 (primary_mul x.property.2.1 x.property.2.1))
  have h := unit_ramified_primary_unique (hp cd) (hp ef) he
  have hc := primary_squarefree_cube_unique cd.property.1 cd.property.2.1
    ef.property.1 ef.property.2.1 cd.property.2.2 ef.property.2.2 h.2.2
  have hcd : cd=ef := Subtype.ext (Prod.ext hc.1 hc.2)
  exact Prod.ext h.1 (Prod.ext h.2.1 hcd)

lemma cubicThetaCommonNumerator_range (n : Eisenstein) :
    n∈Set.range cubicThetaCommonNumerator ↔ Nonempty (CubicThetaCoordinates n) := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨cubicThetaCommonCoordinates x⟩
  · rintro ⟨R⟩
    refine ⟨(R.unit,R.order,⟨(R.squarefreePart,R.cubePart),
      R.squarefree_primary,R.cube_primary,R.squarefree⟩),?_⟩
    exact R.numerator_eq.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonCoefficientBound
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A sharp coordinate majorant for the actual three-cusp coefficient.
The ramified shift lowers its amplitude by three, exactly compensating
for the prefactor in the shifted-cusp expansion. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma CubicThetaCoordinates.coefficient_norm_le_amplitude_common {n : Eisenstein}
    (R : CubicThetaCoordinates n) : ‖R.coefficient‖≤R.amplitude := by
  unfold coefficient
  split_ifs
  · rw [norm_mul,norm_mul,norm_star,cubicThetaUnitPhase_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
    exact mul_le_of_le_one_right R.amplitude_nonneg
      (cubicThetaTwistedGauss_norm_le R.squarefree_primary R.squarefree _)
  · rw [norm_mul,norm_star,norm_gauss_of_squarefree R.squarefree_primary R.squarefree,
      mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
  · simpa only [norm_zero] using R.amplitude_nonneg

lemma cubicThetaArithmetic_coordinate_bound (e : Eisensteinˣ) (k : ℕ)
    {c d : Eisenstein} (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    ‖cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^k*(c*d^3))‖≤
      3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d) := by
  let R : CubicThetaCoordinates ((e:Eisenstein)*lambdaE^k*(c*d^3)) := {
    unit := e
    order := k
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := rfl }
  rw [cubicThetaArithmeticCoefficient_formula R]
  exact R.coefficient_norm_le_amplitude_common

lemma cubicTheta_coordinate_shift_amplitude (k : ℕ) :
    (3:ℝ)*3^(4-(((k+3)/3:ℕ):ℝ))=3^(4-((k/3:ℕ):ℝ)) := by
  have he : (k+3)/3=k/3+1 := by omega
  rw [he]
  push_cast
  rw [show (4-(((k/3:ℕ):ℝ)+1))=(4-((k/3:ℕ):ℝ))-1 by ring]
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<3),Real.rpow_one]
  ring

theorem cubicThetaCommon_coordinate_bound (e : Eisensteinˣ) (k : ℕ)
    {c d : Eisenstein} (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    ‖cubicThetaCommonCuspCoefficient ((e:Eisenstein)*lambdaE^k*(c*d^3))‖≤
      3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d) := by
  let A : ℝ := 3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d)
  have hA : 0≤A := div_nonneg (by positivity)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hb : ‖cubicThetaArithmeticCoefficient (-((e:Eisenstein)*lambdaE^k*(c*d^3)))‖≤A := by
    simpa only [Units.val_neg,neg_mul,A] using
      cubicThetaArithmetic_coordinate_bound (-e) k hc hd hs
  have ht : 3*‖cubicThetaArithmeticCoefficient
      (3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*(c*d^3)))))‖≤A := by
    have he : 3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*(c*d^3))))=
        (e:Eisenstein)*lambdaE^(k+3)*(c*d^3) := by
      have hLam : lambdaE^3= -3*lambdaE := by
        calc
          _ = lambdaE^2*lambdaE := by ring
          _ = _ := by rw [lambdaE_sq]
      rw [pow_add,hLam]
      ring
    rw [he]
    calc
      _ ≤ 3*(3^(4-(((k+3)/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d)) :=
        mul_le_mul_of_nonneg_left (cubicThetaArithmetic_coordinate_bound e (k+3) hc hd hs)
          (by norm_num)
      _ = A := by rw [←mul_div_assoc,cubicTheta_coordinate_shift_amplitude]
  have hb' (j : ℤ) :
      ‖cubicThetaActualCuspCoefficient j (-((e:Eisenstein)*lambdaE^k*(c*d^3)))‖≤A := by
    unfold cubicThetaActualCuspCoefficient
    split_ifs
    · exact hb
    · unfold cubicThetaShiftedLatticeCoefficient
      split_ifs
      · simpa only [norm_mul,Complex.norm_ofNat] using ht
      · simpa only [norm_zero] using hA
  have hw (j : Fin 3) : ‖omega^j.val‖=1 := by
    have ho : ‖omega‖=1 := by
      have h := cubicTheta_unit_norm
        (Units.mkOfMulEqOne omegaE (omegaE^2) (by rw [mul_comm,←pow_succ,omegaE_cube]))
      exact h
    rw [norm_pow,ho,one_pow]
  unfold cubicThetaCommonCuspCoefficient
  rw [norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
  calc
    _ ≤ ∑ j : Fin 3, ‖omega^j.val*
        star (cubicThetaActualCuspCoefficient (j.val:ℤ)
          (-((e:Eisenstein)*lambdaE^k*(c*d^3))))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, A := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_star,hw,one_mul]
      exact hb' _
    _ = A*3 := by simp [mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTwistFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Fourier inversion for the periodic numerator twists in the
cubic theta formula. The trace pairing is perfect for primary moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaResidueChar_mk (q : Eisenstein) (hq : q ≠ 0) (a : Eisenstein) :
    cubicThetaResidueChar q hq (Ideal.Quotient.mk (modulus q) a) =
      (Real.fourierChar (tracePair (a:ℂ) (1/(q:ℂ))):ℂ) := by
  rw [cubicThetaResidueChar,AddChar.mulShift_apply,←map_mul,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  rw [lambdaE_coe]
  field_simp [traceLambda_ne_zero]

lemma cubicThetaResidueChar_primitive {q : Eisenstein} (hq : primary q) :
    (cubicThetaResidueChar q (primary_ne_zero hq)).IsPrimitive := by
  let u : (Residues q)ˣ := (residue_isUnit_of_isCoprime (primary_coprime_lambda hq)).unit
  have hu : (u : Residues q) = Ideal.Quotient.mk (modulus q) lambdaE :=
    (residue_isUnit_of_isCoprime (primary_coprime_lambda hq)).unit_spec
  intro a ha he
  have hna : (u:Residues q)*a ≠ 0 := by
    intro hz
    apply ha
    have h := congrArg (fun x : Residues q => (u⁻¹:((Residues q)ˣ))*x) hz
    simpa only [←mul_assoc,Units.inv_mul,mul_zero,one_mul] using h
  apply residueFourierChar_isPrimitive q (primary_ne_zero hq)
    (a := (u:Residues q)*a) hna
  simpa only [cubicThetaResidueChar,AddChar.mulShift_mulShift,←hu] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamanujan
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Ramanujan sum in the trace normalization of the actual
cubic theta series. Its weight is the cube of the cubic residue character. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaSymbol_cube_indicator {r : Eisenstein} (hr : primary r) (x : Eisenstein) :
    cubicSymbol r x^3=(if IsCoprime r x then 1 else 0) := by
  by_cases hx : IsCoprime r x
  · rw [ite_eq_left hx,cubicSymbol_cube_of_isCoprime hr x hx]
  · rw [ite_eq_right hx,cubicSymbol_eq_zero_of_not_isCoprime hr hx]
    norm_num

lemma cubicThetaRamanujan_prime {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaRamanujan p h=if p∣h then (norm p:ℂ)-1 else -1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let χ := cubicThetaResidueChar p hp.2.ne_zero
  let a := Ideal.Quotient.mk (modulus p) h
  have ha : a=0 ↔ p∣h := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton
  have hc (x : Residues p) : IsCoprime p (residueRepresentative p x) ↔ x≠0 := by
    constructor
    · intro hx
      have hu := residue_isUnit_of_isCoprime hx
      rw [residueRepresentative_spec,isUnit_iff_ne_zero] at hu
      exact hu
    · intro hx
      apply isCoprime_of_residue_isUnit
      rw [residueRepresentative_spec]
      exact isUnit_iff_ne_zero.mpr hx
  have he (x : Residues p) : additivePhase p (h*residueRepresentative p x)=χ (a*x) := by
    rw [additivePhase_fourierChar]
    have hh := cubicThetaResidueChar_mk p hp.2.ne_zero (h*residueRepresentative p x)
    rw [map_mul,residueRepresentative_spec] at hh
    exact hh.symm
  rw [cubicThetaRamanujan,tsum_fintype]
  simp_rw [cubicThetaSymbol_cube_indicator hp.1,hc,he]
  have hs : (∑ x : Residues p,(if x≠0 then (1:ℂ) else 0)*χ (a*x))=
      (∑ x : Residues p,χ (a*x))-1 := by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [ne_eq,not_true_eq_false,ite_false, if_false,mul_zero,zero_mul,χ.map_zero_eq_one,add_zero]
    rw [eq_sub_iff_add_eq]
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [mul_zero,χ.map_zero_eq_one]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [ite_eq_left (Finset.ne_of_mem_erase hx),one_mul]
  rw [hs]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift a (cubicThetaResidueChar_primitive hp.1),ha]
  have hn : (Fintype.card (Residues p):ℂ)=(norm p:ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  split_ifs <;> simp_all

lemma cubicThetaRamanujan_one (h : Eisenstein) : cubicThetaRamanujan 1 h=1 := by
  have he := frequencyGauss_one h
  have hn : norm (1:Eisenstein)=1 := by norm_num [norm]
  rw [frequencyGauss,hn,Real.sqrt_one,Complex.ofReal_one,inv_one,one_mul] at he
  simpa only [frequencyGauss,cubicThetaRamanujan,cubicSymbol_one_lower,one_pow,one_mul,
    norm_one,Real.sqrt_one,Complex.ofReal_one,inv_one] using he

lemma cubicThetaRamanujan_mul {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) (h : Eisenstein) :
    cubicThetaRamanujan (a*b) h=cubicThetaRamanujan a h*cubicThetaRamanujan b h := by
  let : Finite (Residues a) := finite_residues (primary_ne_zero ha)
  let : Finite (Residues b) := finite_residues (primary_ne_zero hb)
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b)
    (residueMix_bijective (primary_ne_zero ha) (primary_ne_zero hb) hab)
  let f (q : Eisenstein) (x : Residues q) : ℂ :=
    cubicSymbol q (residueRepresentative q x)^3*additivePhase q (h*residueRepresentative q x)
  have ht (v : Residues a × Residues b) : f (a*b) (e v)=f a v.1*f b v.2 := by
    have heq : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v))=
        Ideal.Quotient.mk (modulus (a*b))
          (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    have heqh : Ideal.Quotient.mk (modulus (a*b)) (h*residueRepresentative (a*b) (e v))=
        Ideal.Quotient.mk (modulus (a*b))
          (h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2)) := by
      rw [map_mul,map_mul,heq]
    dsimp only [f]
    rw [cubicSymbol_congr heq]
    rw [additivePhase_congr (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
      heqh]
    rw [cubicSymbol_mix ha hb,mul_pow,mul_pow,mul_pow,
      cubicSymbol_cube_of_isCoprime ha b hab,cubicSymbol_cube_of_isCoprime hb a hab.symm]
    rw [show h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2)=
      b*(h*residueRepresentative a v.1)+a*(h*residueRepresentative b v.2) by ring,
      additivePhase_mix (primary_ne_zero ha) (primary_ne_zero hb)]
    ring
  simp only [cubicThetaRamanujan,tsum_fintype]
  change (∑ x : Residues (a*b),f (a*b) x)=(∑ x,f a x)*(∑ x,f b x)
  rw [←Equiv.sum_comp e (f (a*b))]
  simp_rw [ht]
  rw [Fintype.sum_prod_type,←Finset.sum_mul_sum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamanujanProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Ramanujan average is precisely the squarefree local
Euler coefficient in the published Voronoi formula. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaRamanujan_prod (s : Finset Eisenstein)
    (hp : ∀ p∈s,primaryPrime p) (h : Eisenstein) :
    cubicThetaRamanujan (∏ p∈s,p) h=
      ∏ p∈s,if p∣h then (norm p:ℂ)-1 else -1 := by
  induction s using Finset.induction_on with
  | empty => simp [cubicThetaRamanujan_one]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q∈s,primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hprimary := primary_finset_prod s (fun q => q) (fun q hq => (hs q hq).1)
    have hc : IsCoprime p (∏ q∈s,q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun heq => hps (heq ▸ hq))
    rw [Finset.prod_insert hps,cubicThetaRamanujan_mul hp'.1 hprimary hc,
      cubicThetaRamanujan_prime hp',ih hs,Finset.prod_insert hps]

theorem cubicThetaRamanujan_squarefree {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) (n : MetaplecticDualArgument) :
    cubicThetaRamanujan r n.val=metaplecticLocalCoefficient r n := by
  calc
    _ = ∏ p∈primaryPrimeFactors r,if p∣n.val then (norm p:ℂ)-1 else -1 := by
      conv_lhs => rw [←primaryPrimeFactors_prod hr hs]
      exact cubicThetaRamanujan_prod _ (fun p hp => (primaryPrimeFactor_spec hr hp).1) n.val
    _ = _ := by
      unfold metaplecticLocalCoefficient
      apply Finset.prod_congr rfl
      intro p _
      split_ifs <;> push_cast <;> rfl

lemma cubicTheta_sum_eq_units {R : Type*} [CommRing R] [Fintype R]
    (f : R→ℂ) (hf : ∀ x,¬IsUnit x→f x=0) :
    (∑ x : R,f x)=∑ u : Rˣ,f u := by
  have hs : Function.support f ⊆ {x | IsUnit x} := by
    intro x hx
    by_contra hu
    exact hx (hf x hu)
  let e := (Submonoid.unitsTypeEquivIsUnitSubmonoid (M:=R)).toEquiv
  calc
    _ = ∑' x : R,f x := (tsum_fintype _).symm
    _ = ∑' x : {x : R // IsUnit x},f x := (tsum_subtype_eq_of_support_subset hs).symm
    _ = ∑' u : Rˣ,f u := (e.tsum_eq (fun x => f x.val)).symm
    _ = _ := tsum_fintype _

theorem cubicThetaRamanujan_units {r : Eisenstein} (hr : primary r)
    [Fintype (Residues r)] (h : Eisenstein) :
    cubicThetaRamanujan r h=
      ∑ u : (Residues r)ˣ,additivePhase r (h*residueRepresentative r u) := by
  rw [cubicThetaRamanujan,tsum_fintype]
  have hz (x : Residues r) (hx : ¬IsUnit x) :
      cubicSymbol r (residueRepresentative r x)^3*additivePhase r (h*residueRepresentative r x)=0 := by
    have hn : ¬IsCoprime r (residueRepresentative r x) := by
      intro hh
      exact hx (by simpa only [residueRepresentative_spec] using residue_isUnit_of_isCoprime hh)
    rw [cubicThetaSymbol_cube_indicator hr,ite_eq_right hn,zero_mul]
  rw [cubicTheta_sum_eq_units _ hz]
  apply Finset.sum_congr rfl
  intro u _
  have hu : IsCoprime r (residueRepresentative r u) := by
    apply isCoprime_of_residue_isUnit
    rw [residueRepresentative_spec]
    exact u.isUnit
  rw [cubicThetaSymbol_cube_indicator hr,ite_eq_left hu,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeCancellation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primary-cube scaling of the actual dual coefficient and its
local Ramanujan factor. These are the algebraic inputs to free-cube removal. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFrequency_mul_cube (n d : Eisenstein) :
    cubicThetaFrequency (n*d^3)=cubicThetaFrequency n*(d:ℂ)^3 := by
  unfold cubicThetaFrequency
  push_cast
  ring

lemma cubicThetaLocalCoefficient_cube {r d : Eisenstein} (hr : primary r)
    (hd : primary d) (hcop : IsCoprime d r) (n : MetaplecticDualArgument) :
    metaplecticLocalCoefficient r (cubicThetaDualCube d hd n)=
      metaplecticLocalCoefficient r n := by
  unfold metaplecticLocalCoefficient
  apply Finset.prod_congr rfl
  intro p hp
  have hs := primaryPrimeFactor_spec hr hp
  have hpd : ¬p∣d := fun h => hs.1.2.not_isUnit (hcop.isUnit_of_dvd' h hs.2)
  have he : p∣n.val*d^3 ↔ p∣n.val := by
    constructor
    · intro h
      rcases hs.1.2.dvd_mul.mp h with h | h
      · exact h
      · exact False.elim (hpd (hs.1.2.dvd_of_dvd_pow h))
    · intro h
      exact dvd_mul_of_dvd_left h _
  simp only [cubicThetaDualCube,he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonTauBound
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual unnormalized dual coefficient has the ramified growth and
square-root cube-factor bound required for the local summation formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_coordinate_norm (e : Eisensteinˣ) (k : ℕ) (c d : Eisenstein) :
    ‖cubicThetaFrequency ((e:Eisenstein)*lambdaE^k*(c*d^3))‖=
      (Real.sqrt 3)^k*Real.sqrt (norm c)*(Real.sqrt (norm d))^3/9 := by
  have hr (a : Eisenstein) : Real.sqrt (norm a)=‖(a:ℂ)‖ := by
    rw [norm,Complex.normSq_eq_norm_sq,Real.sqrt_sq (_root_.norm_nonneg _)]
  have hl : Real.sqrt (norm lambdaE)=Real.sqrt 3 := by
    rw [norm,lambdaE_coe,traceLambda_normSq]
  rw [cubicThetaFrequency_div_nine,norm_div,Complex.norm_ofNat]
  simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,norm_mul,norm_pow,
    cubicTheta_unit_norm,one_mul]
  rw [←hr lambdaE,←hr c,←hr d,hl]
  ring

lemma cubicTheta_coordinate_amplitude_product (k : ℕ) {c d : Eisenstein}
    (hc : primary c) (hd : primary d) :
    ((Real.sqrt 3)^k*Real.sqrt (norm c)*(Real.sqrt (norm d))^3/9)*
      (3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d))=
        9*3^((k:ℝ)/2-((k/3:ℕ):ℝ))*Real.sqrt (norm d) := by
  have hc0 := (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hc))).ne'
  have hd0 := (norm_pos_of_ne_zero (primary_ne_zero hd)).ne'
  have hp : (Real.sqrt 3)^k*3^(4-((k/3:ℕ):ℝ))/9=
      9*3^((k:ℝ)/2-((k/3:ℕ):ℝ)) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),
      ←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    calc
      _ = 3^((1/2:ℝ)*k+(4-((k/3:ℕ):ℝ)))/3^(2:ℝ) := by rw [Real.rpow_two]; norm_num
      _ = 3^((1/2:ℝ)*k+(4-((k/3:ℕ):ℝ))-2) :=
        (Real.rpow_sub (by norm_num : (0:ℝ)<3) _ _).symm
      _ = _ := by
        rw [show (1/2:ℝ)*k+(4-((k/3:ℕ):ℝ))-2=
          2+((k:ℝ)/2-((k/3:ℕ):ℝ)) by ring,
          Real.rpow_add (by norm_num : (0:ℝ)<3),Real.rpow_two]
        norm_num
  calc
    _ = ((Real.sqrt 3)^k*3^(4-((k/3:ℕ):ℝ))/9)*Real.sqrt (norm d) := by
      field_simp
      rw [show (Real.sqrt (norm d))^3=Real.sqrt (norm d)*(Real.sqrt (norm d))^2 by ring,
        Real.sq_sqrt (norm_nonneg d)]
    _ = _ := by rw [hp]

lemma cubicTheta_ramified_growth_exponent (k : ℕ) :
    (k:ℝ)/2-((k/3:ℕ):ℝ) ≤ ((max ((k:ℤ)-1) 0:ℤ):ℝ)/3+1 := by
  have hq : k≤3*(k/3)+2 := by omega
  have hq' : (k:ℝ)≤3*((k/3:ℕ):ℝ)+2 := by exact_mod_cast hq
  have hm : (k:ℝ)-1≤((max ((k:ℤ)-1) 0:ℤ):ℝ) := by
    exact_mod_cast (le_max_left ((k:ℤ)-1) 0)
  have hk : 0≤(k:ℝ) := Nat.cast_nonneg k
  linarith

theorem cubicThetaCommonTau_coordinate_bound (e : Eisensteinˣ) (k : ℕ)
    {c d : Eisenstein} (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    ‖cubicThetaCommonTau ((e:Eisenstein)*lambdaE^k*(c*d^3))‖≤
      27*3^(((max ((k:ℤ)-1) 0:ℤ):ℝ)/3)*Real.sqrt (norm d) := by
  unfold cubicThetaCommonTau
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
  calc
    _ ≤ ‖cubicThetaFrequency ((e:Eisenstein)*lambdaE^k*(c*d^3))‖*
        (3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d)) :=
      mul_le_mul_of_nonneg_left (cubicThetaCommon_coordinate_bound e k hc hd hs)
        (_root_.norm_nonneg _)
    _ = 9*3^((k:ℝ)/2-((k/3:ℕ):ℝ))*Real.sqrt (norm d) := by
      rw [cubicThetaFrequency_coordinate_norm,cubicTheta_coordinate_amplitude_product k hc hd]
    _ ≤ 9*3^(((max ((k:ℤ)-1) 0:ℤ):ℝ)/3+1)*Real.sqrt (norm d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
            (cubicTheta_ramified_growth_exponent k)) (by norm_num))
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<3),Real.rpow_one]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueCusps
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational-cusp lift on every residue. Nonunit residues get
an arbitrary determinant-one lift, and their cubic character weight is zero. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaProjectedCoefficient_congr {g h : SL(2,Eisenstein)} (he : g=h)
    (hg : primary (g 1 0)) (hh : primary (h 1 0)) :
    cubicThetaProjectedCoefficient g hg = cubicThetaProjectedCoefficient h hh := by
  subst h
  rfl

lemma cubicThetaResidueCuspMatrix_of_coprime (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaResidueCuspMatrix r hr u = cubicThetaNineGaussMatrix r hr u hu := by
  exact dite_eq_left hu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaVoronoiScale
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact frequency bookkeeping for the constructed transform. The common
cusp numerator `n` represents `n/lambda^4`; the published dual argument
represents `n/lambda`. The conversion is recorded without changing either
normalization or identifying the two transform arguments. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_metaplectic_normSq (n : MetaplecticDualArgument) :
    Complex.normSq (metaplecticFrequency n)=norm n.val/3 := by
  rw [metaplecticFrequency,Complex.normSq_div,traceLambda_normSq]
  rfl

lemma cubicThetaLevelScale_fourth {r : Eisenstein} (_hr : primary r) :
    cubicThetaLevelScale r^4=(norm r^2)⁻¹ := by
  have hs := Real.sq_sqrt (norm_nonneg r)
  unfold cubicThetaLevelScale
  rw [inv_pow]
  congr 1
  nlinarith [sq_nonneg (Real.sqrt (norm r))]

lemma cubicThetaVoronoi_dual_argument {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (X : ℝ) :
    cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2=
      (2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/(729*norm r^2) := by
  rw [cubicThetaDualScale,cubicThetaLevelScale_fourth hr,cubicThetaFrequency_sq,
    cubicTheta_metaplectic_normSq]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreCoefficient
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete dual coefficient after free-cube removal. Its support
and the required ramified coefficient bound are proved from the actual
three-cusp arithmetic formulas. The summation identity is separate. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma CubicThetaCoordinates.metaplectic_frequency {n : Eisenstein}
    (R : CubicThetaCoordinates n) (hn : n≠0) :
    metaplecticFrequency ⟨n,hn⟩=traceLambda^((R.order:ℤ)-1)*(R.unit:Eisenstein)*
      (R.squarefreePart:ℂ)*(R.cubePart:ℂ)^3 := by
  have hp : traceLambda^((R.order:ℤ)-1)*traceLambda=traceLambda^R.order := by
    calc
      _ = traceLambda^((R.order:ℤ)-1)*traceLambda^(1:ℤ) := by rw [zpow_one]
      _ = _ := by rw [←zpow_add₀ traceLambda_ne_zero,sub_add_cancel,zpow_natCast]
  apply mul_right_cancel₀ traceLambda_ne_zero
  rw [metaplecticFrequency,div_mul_cancel₀ _ traceLambda_ne_zero]
  calc
    _ = (R.unit:Eisenstein)*traceLambda^R.order*
        (R.squarefreePart:ℂ)*(R.cubePart:ℂ)^3 := by
      change (n:ℂ)=_
      conv_lhs => rw [R.numerator_eq]
      push_cast
      rw [lambdaE_coe]
      ring
    _ = _ := by rw [←hp]; ring

theorem cubicThetaCoreCoefficient_bounds :
    MetaplecticCoefficientBounds cubicThetaCoreCoefficient := by
  refine ⟨27,by norm_num,?_⟩
  intro r hr _hs n hne
  have hs : CubicThetaCoreSupport r n := by
    by_contra h
    simp only [cubicThetaCoreCoefficient,ite_eq_right h,zero_mul,ne_eq,not_true_eq_false] at hne
  obtain ⟨R,k,hk⟩ := hs
  let h := primarySmallPart r R.squarefreePart
  let w := primaryOutsidePart r R.squarefreePart
  have hh : primary h := primarySmallPart_primary r R.squarefree_primary
  have hw : primary w := primaryOutsidePart_primary r R.squarefree_primary
  have hc : h*w=R.squarefreePart := primary_small_outside_mul r R.squarefree_primary
  refine ⟨(R.order:ℤ)-1,R.unit,h,R.cubePart,w,by omega,hh,R.cube_primary,hw,
    cubicTheta_primarySmallPart_supported (primary_ne_zero hr) R.squarefree_primary,
    ⟨k,hk⟩,primaryOutsidePart_coprime R.squarefree_primary (primary_ne_zero hr),?_,?_,?_⟩
  · rw [hc]
    exact R.squarefree
  · have he := R.metaplectic_frequency n.property
    rw [←hc] at he
    simpa only [Subalgebra.coe_mul,mul_assoc] using he
  · rw [cubicThetaCoreCoefficient,ite_eq_left ⟨R,k,hk⟩]
    conv_lhs => rw [R.numerator_eq]
    exact cubicThetaCommonTau_coordinate_bound R.unit R.order R.squarefree_primary
      R.cube_primary R.squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeCubeIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An exact bijection separating every primary cube factor into the
part supported on the level and the free part. No multiplicity is lost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicTheta_free_cube_tsum {r : Eisenstein} (hr : r≠0)
    (f : CubicThetaCommonIndex→ℂ) :
    (∑' x : CubicThetaCommonIndex,f x)=
      ∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,f (cubicThetaFreeCubeJoin r x) :=
  ((cubicThetaFreeCubeEquiv r hr).tsum_eq f).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNineDualPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A lower-right entry divisible by nine identifies the actual dual
phase with an ordinary residue-ring additive character. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicTheta_additivePhase_one (a : Eisenstein) : additivePhase 1 a=1 := by
  rw [additivePhase_congr one_ne_zero (residue_eq_of_dvd_sub (one_dvd (a-0))),additivePhase_zero]

lemma cubicTheta_trace_integral_phase (a : Eisenstein) :
    (Real.fourierChar (tracePair (a:ℂ) 1):ℂ)=1 := by
  simpa only [additivePhase_fourierChar,Subalgebra.coe_one,div_one] using cubicTheta_additivePhase_one a

lemma cubicThetaNineDual_phase (g : SL(2,Eisenstein)) (r δ : Eisenstein)
    (hc : g 1 0=r) (hd : g 1 1=9*δ) (n : Eisenstein) :
    (Real.fourierChar (tracePair (cubicThetaFrequency n) (cubicThetaPrimaryDualCenter g)):ℂ)=
      additivePhase r (-n*δ) := by
  have he : tracePair (cubicThetaFrequency n) (cubicThetaPrimaryDualCenter g)=
      tracePair ((n*δ:Eisenstein):ℂ) 1+
        tracePair ((-n*δ:Eisenstein):ℂ) (1/(r:ℂ)) := by
    rw [cubicThetaFrequency_div_nine]
    unfold cubicThetaPrimaryDualCenter
    rw [hc,hd]
    unfold tracePair
    push_cast
    simp only [mul_one,one_div]
    rw [←mul_add,←Complex.add_re]
    rw [show ((9:Eisenstein):ℂ)=(9:ℂ) from rfl]
    congr 2
    ring
  rw [he,AddChar.map_add_eq_mul,Circle.coe_mul,cubicTheta_trace_integral_phase,one_mul]
  exact (additivePhase_fourierChar _ _).symm

lemma cubicThetaNineGaussMatrix_weighted_coefficient (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (δ : Eisenstein)
    (hd : cubicThetaNineGaussMatrix r hr u hu 1 1=9*δ) (n : Eisenstein) :
    cubicSymbol r u*cubicThetaCoefficientTwist
      (cubicThetaProjectedCoefficient (cubicThetaNineGaussMatrix r hr u hu)
        (cubicThetaNineGaussMatrix_primary r hr u hu))
      (cubicThetaPrimaryDualCenter (cubicThetaNineGaussMatrix r hr u hu)) n=
      cubicThetaCommonCuspCoefficient n*additivePhase r (-n*δ) := by
  rw [cubicThetaCoefficientTwist,cubicThetaNineGaussMatrix_coefficient,
    cubicThetaNineDual_phase _ r δ (cubicThetaNineGaussMatrix_entries r hr u hu).2.1 hd]
  have he : cubicSymbol r u*star (cubicSymbol r u)=1 := by
    rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hr hu]
    norm_num
  calc
    _ = (cubicSymbol r u*star (cubicSymbol r u))*
      (cubicThetaCommonCuspCoefficient n*additivePhase r (-n*δ)) := by ring
    _ = _ := by rw [he,one_mul]

lemma cubicThetaNineGaussMatrix_inverse (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (δ : Eisenstein)
    (hd : cubicThetaNineGaussMatrix r hr u hu 1 1=9*δ) :
    r∣(9*lambdaE^3*u*δ)-1 := by
  let g := cubicThetaNineGaussMatrix r hr u hu
  have he : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1,
    (cubicThetaNineGaussMatrix_entries r hr u hu).2.1,hd] at he
  refine ⟨g 0 1,?_⟩
  linear_combination he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInverseResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse residues arising from determinant-one cusp lifts permute
the actual unit group. No distribution or cancellation estimate is assumed. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaNineConductorUnit_val (r : Eisenstein) (hr : primary r) :
    (cubicThetaNineConductorUnit r hr:Residues r)=
      Ideal.Quotient.mk (modulus r) (9*lambdaE^3) :=
  (residue_isUnit_of_isCoprime
    ((cubicTheta_coprime_nine hr).mul_right ((primary_coprime_lambda hr).pow_right (n:=3)))).unit_spec

lemma cubicThetaNineUnitInverse_spec (r : Eisenstein) (hr : primary r) (u : (Residues r)ˣ) :
    cubicThetaNineGaussMatrix r hr (residueRepresentative r u)
      (cubicThetaUnitRepresentative_coprime r u) 1 1=9*cubicThetaNineUnitInverse r hr u :=
  Classical.choose_spec (cubicThetaNineGaussMatrix_nine r hr (residueRepresentative r u)
    (cubicThetaUnitRepresentative_coprime r u))

lemma cubicThetaNineUnitInverse_residue (r : Eisenstein) (hr : primary r) (u : (Residues r)ˣ) :
    Ideal.Quotient.mk (modulus r) (cubicThetaNineUnitInverse r hr u)=
      (((cubicThetaNineConductorUnit r hr*u)⁻¹ : (Residues r)ˣ):Residues r) := by
  let A := cubicThetaNineConductorUnit r hr
  let δ := cubicThetaNineUnitInverse r hr u
  have hd := cubicThetaNineGaussMatrix_inverse r hr (residueRepresentative r u)
    (cubicThetaUnitRepresentative_coprime r u) δ (cubicThetaNineUnitInverse_spec r hr u)
  have he := residue_eq_of_dvd_sub hd
  have hp : ((A*u:(Residues r)ˣ):Residues r)*Ideal.Quotient.mk (modulus r) δ=1 := by
    rw [Units.val_mul,cubicThetaNineConductorUnit_val]
    simpa only [map_mul,map_pow,map_one,residueRepresentative_spec,mul_assoc] using he
  have hi : (((A*u)⁻¹:(Residues r)ˣ):Residues r)*((A*u:(Residues r)ˣ):Residues r)=1 :=
    (A*u).inv_mul
  change Ideal.Quotient.mk (modulus r) δ=_
  calc
    _ = 1*Ideal.Quotient.mk (modulus r) δ := (one_mul _).symm
    _ = ((((A*u)⁻¹:(Residues r)ˣ):Residues r)*((A*u:(Residues r)ˣ):Residues r))*
        Ideal.Quotient.mk (modulus r) δ := by rw [hi]
    _ = (((A*u)⁻¹:(Residues r)ˣ):Residues r)*
        (((A*u:(Residues r)ˣ):Residues r)*Ideal.Quotient.mk (modulus r) δ) := mul_assoc _ _ _
    _ = _ := by rw [hp,mul_one]

theorem cubicThetaNineUnitInverse_average (r : Eisenstein) (hr : primary r)
    [Fintype (Residues r)] (n : Eisenstein) :
    (∑ u : (Residues r)ˣ,additivePhase r (-n*cubicThetaNineUnitInverse r hr u))=
      cubicThetaRamanujan r n := by
  let A := cubicThetaNineConductorUnit r hr
  let e : Equiv.Perm ((Residues r)ˣ) :=
    ((Equiv.mulLeft A).trans (Equiv.inv _)).trans (Equiv.neg _)
  have he (u : (Residues r)ˣ) : (e u:Residues r)=
      -((((A*u)⁻¹:(Residues r)ˣ):Residues r)) := rfl
  have ht (u : (Residues r)ˣ) :
      additivePhase r (-n*cubicThetaNineUnitInverse r hr u)=
        additivePhase r (n*residueRepresentative r (e u)) := by
    apply additivePhase_congr (primary_ne_zero hr)
    rw [map_mul,map_mul,residueRepresentative_spec,he,map_neg,
      cubicThetaNineUnitInverse_residue]
    ring
  simp_rw [ht]
  calc
    _ = ∑ u : (Residues r)ˣ, additivePhase r (n*residueRepresentative r u) :=
      Equiv.sum_comp e (fun u : (Residues r)ˣ => additivePhase r (n*residueRepresentative r u))
    _ = _ := (cubicThetaRamanujan_units hr n).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueLocalCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite dual cusp coefficient equals the universal
three-cusp coefficient times the exact local Ramanujan product. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicThetaResidueDualCoefficient_local {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) [Fintype (Residues r)] (n : MetaplecticDualArgument) :
    cubicThetaResidueDualCoefficient r hr n.val=
      cubicThetaCommonCuspCoefficient n.val*metaplecticLocalCoefficient r n := by
  let F (x : Residues r) : ℂ := cubicSymbol r (residueRepresentative r x)*
    cubicThetaCoefficientTwist
      (cubicThetaProjectedCoefficient (cubicThetaResidueCuspMatrix r hr (residueRepresentative r x))
        (cubicThetaResidueCuspPrimary r hr (residueRepresentative r x)))
      (cubicThetaPrimaryDualCenter (cubicThetaResidueCuspMatrix r hr (residueRepresentative r x))) n.val
  have hz (x : Residues r) (hx : ¬IsUnit x) : F x=0 := by
    have hn : ¬IsCoprime r (residueRepresentative r x) := by
      intro h
      exact hx (by simpa only [residueRepresentative_spec] using residue_isUnit_of_isCoprime h)
    dsimp only [F]
    rw [cubicSymbol_eq_zero_of_not_isCoprime hr hn,zero_mul]
  have ht (u : (Residues r)ˣ) : F u=
      cubicThetaCommonCuspCoefficient n.val*
        additivePhase r (-n.val*cubicThetaNineUnitInverse r hr u) := by
    have hu := cubicThetaUnitRepresentative_coprime r u
    have hg := cubicThetaResidueCuspMatrix_of_coprime r hr _ hu
    have ha := cubicThetaProjectedCoefficient_congr hg
      (cubicThetaResidueCuspPrimary r hr _) (cubicThetaNineGaussMatrix_primary r hr _ hu)
    have hz := congrArg cubicThetaPrimaryDualCenter hg
    dsimp only [F,cubicThetaCoefficientTwist]
    rw [ha,hz]
    have H := cubicThetaNineGaussMatrix_weighted_coefficient r hr (residueRepresentative r u) hu
      (cubicThetaNineUnitInverse r hr u) (cubicThetaNineUnitInverse_spec r hr u) n.val
    exact H
  change (∑ x : Residues r,F x)=_
  rw [cubicTheta_sum_eq_units F hz]
  simp_rw [ht]
  rw [←Finset.mul_sum,cubicThetaNineUnitInverse_average,cubicThetaRamanujan_squarefree hr hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonzero-angular summation formula with the finite cusp
average evaluated as its exact Ramanujan Euler product. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubicThetaResidueDualTerm_local {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) [Fintype (Residues r)] (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    cubicThetaResidueDualTerm r hr rev k W σ X=cubicThetaLocalDualTerm r rev k W σ X := by
  funext n
  unfold cubicThetaResidueDualTerm cubicThetaLocalDualTerm
  rw [cubicThetaResidueDualCoefficient_local hr hs]

theorem cubicThetaLocal_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (cubicThetaLocalDualTerm r rev k W σ X) ∧
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      ∑' n,cubicThetaLocalDualTerm r rev k W σ X n := by
  have H := cubicThetaResidue_voronoi hr hs rev hk W hW hpos hsm hσ hX
  rwa [cubicThetaResidueDualTerm_local hr hs] at H

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalCubeTerm
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact free-cube denominator and transform argument in each actual
local dual term. The exponent 5/2 is derived, not assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_norm_sqrt (d : Eisenstein) : ‖(d:ℂ)‖=Real.sqrt (norm d) := by
  rw [norm,Complex.normSq_eq_norm_sq,Real.sqrt_sq (_root_.norm_nonneg _)]

lemma cubicTheta_five_halves (d : Eisenstein) :
    norm d^(5/2:ℝ)=norm d*(Real.sqrt (norm d))^3 := by
  by_cases hd : d=0
  · subst d
    norm_num [norm]
  · rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast (norm_nonneg d),
      show (5/2:ℝ)=1+(1/2:ℝ)*3 by norm_num,
      Real.rpow_add (norm_pos_of_ne_zero hd),Real.rpow_one]
    norm_num

lemma cubicThetaFrequency_cube_norm (n d : Eisenstein) :
    ‖cubicThetaFrequency (n*d^3)‖=‖cubicThetaFrequency n‖*(Real.sqrt (norm d))^3 := by
  rw [cubicThetaFrequency_mul_cube,norm_mul,norm_pow,cubicTheta_norm_sqrt]

lemma cubicThetaFrequency_cube_square (n d : Eisenstein) :
    ‖cubicThetaFrequency (n*d^3)‖^2=‖cubicThetaFrequency n‖^2*norm d^3 := by
  rw [cubicThetaFrequency_cube_norm,mul_pow,←pow_mul,
    show (3:ℕ)*2=2*3 by norm_num,pow_mul,Real.sq_sqrt (norm_nonneg d)]

theorem cubicThetaLocalDualTerm_cube {r d : Eisenstein} (hr : primary r)
    (hd : primary d) (hcop : IsCoprime d r) (n : MetaplecticDualArgument)
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ) :
    cubicThetaLocalDualTerm r rev k W σ X (cubicThetaDualCube d hd n)=
      theta (cubicThetaCircleOrder rev k) (n.val*d^3)*
        (cubicThetaCommonTau n.val*metaplecticLocalCoefficient r n)/
          ((‖cubicThetaFrequency n.val‖^2*norm d^(5/2:ℝ):ℝ):ℂ)*
            metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
              (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2*norm d^3) := by
  have hn0 : (‖cubicThetaFrequency n.val‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaFrequency_pos n.property).ne'
  have hd0 : (norm d:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (primary_ne_zero hd)).ne'
  have hds0 : (Real.sqrt (norm d):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hd))).ne'
  unfold cubicThetaLocalDualTerm
  rw [cubicThetaLocalCoefficient_cube hr hd hcop]
  dsimp only [cubicThetaDualCube]
  change theta _ (n.val*d^3)*
    (cubicThetaCommonCuspCoefficient (n.val*d^3)*metaplecticLocalCoefficient r n)/
      (‖cubicThetaFrequency (n.val*d^3)‖:ℂ)*_= _
  rw [cubicThetaCommonCuspCoefficient_primaryCube d hd,cubicThetaFrequency_cube_square,
    cubicThetaFrequency_cube_norm,cubicTheta_five_halves,cubicThetaCommonTau]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  congr 1
  · field_simp
  · congr 1
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeLocalVoronoi
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete angular transform with the free cube variable separated.
Both its coefficient bound and its absolutely convergent sum are proved. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubicThetaCommonArgument_injective : Function.Injective cubicThetaCommonArgument := by
  intro x y he
  exact cubicThetaCommonNumerator_injective (congrArg Subtype.val he)

lemma cubicThetaLocalDualTerm_reindex {r : Eisenstein} (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    (∑' n,cubicThetaLocalDualTerm r rev k W σ X n)=
      ∑' x : CubicThetaCommonIndex,
        cubicThetaLocalDualTerm r rev k W σ X (cubicThetaCommonArgument x) := by
  apply (cubicThetaCommonArgument_injective.tsum_eq ?_).symm
  intro n hn
  have ha : cubicThetaCommonCuspCoefficient n.val≠0 := by
    intro h
    exact hn (by simp [cubicThetaLocalDualTerm,h])
  obtain ⟨x,hx⟩ := (cubicThetaCommonNumerator_range n.val).mpr
    (cubicThetaCommonCuspCoefficient_support n.property ha)
  exact ⟨x,Subtype.ext hx⟩

lemma cubicThetaCoreCoefficient_index (r : Eisenstein) (x : CubicThetaCoreIndex r) :
    cubicThetaCoreCoefficient r (cubicThetaCommonArgument x.val)=
      cubicThetaCommonTau (cubicThetaCommonNumerator x.val) := by
  unfold cubicThetaCoreCoefficient
  apply ite_eq_left
  exact ⟨cubicThetaCommonCoordinates x.val,x.property⟩

lemma cubicThetaFreeCubeJoin_argument (r : Eisenstein)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    cubicThetaCommonArgument (cubicThetaFreeCubeJoin r x)=
      cubicThetaDualCube (x.2.val:Eisenstein) x.2.val.property
        (cubicThetaCommonArgument x.1.val) := by
  apply Subtype.ext
  change cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x)=
    cubicThetaCommonNumerator x.1.val*(x.2.val:Eisenstein)^3
  unfold cubicThetaCommonNumerator cubicThetaFreeCubeJoin
  ring

lemma cubicThetaFreeLocalDualTerm_eq {r : Eisenstein} (hr : primary r)
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    cubicThetaLocalDualTerm r rev k W σ X
      (cubicThetaCommonArgument (cubicThetaFreeCubeJoin r x))=
        cubicThetaFreeLocalDualTerm r rev k W σ X x := by
  rw [cubicThetaFreeCubeJoin_argument,cubicThetaLocalDualTerm_cube hr x.2.val.property x.2.property]
  unfold cubicThetaFreeLocalDualTerm
  rw [cubicThetaCoreCoefficient_index]
  have he := congrArg Subtype.val (cubicThetaFreeCubeJoin_argument r x)
  change cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x)=
    cubicThetaCommonNumerator x.1.val*(x.2.val:Eisenstein)^3 at he
  rw [he]
  rfl

theorem cubicThetaFree_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (cubicThetaFreeLocalDualTerm r rev k W σ X) ∧
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      ∑' x,cubicThetaFreeLocalDualTerm r rev k W σ X x := by
  obtain ⟨hS,hE⟩ := cubicThetaLocal_voronoi hr hs rev hk W hW hpos hsm hσ hX
  have hI := hS.comp_injective cubicThetaCommonArgument_injective
  have hJ := hI.comp_injective (cubicThetaFreeCubeJoin_injective (primary_ne_zero hr))
  have he := cubicThetaFreeLocalDualTerm_eq hr rev k W σ X
  refine ⟨hJ.congr he,?_⟩
  rw [cubicThetaLocalDualTerm_reindex,
    cubicTheta_free_cube_tsum (primary_ne_zero hr)] at hE
  simpa only [he] using hE

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreArguments
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported core indices and free primary factors give exactly the
nonzero domain of the full dual sum, with all zero extensions retained. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaCoreArgument_injective (r : Eisenstein) :
    Function.Injective (cubicThetaCoreArgument (r:=r)) := by
  intro x y he
  exact Subtype.ext (cubicThetaCommonArgument_injective he)

lemma cubicThetaCoreArgument_range (r : Eisenstein) (n : MetaplecticDualArgument) :
    n∈Set.range (cubicThetaCoreArgument (r:=r)) ↔ CubicThetaCoreSupport r n := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨cubicThetaCommonCoordinates x.val,x.property⟩
  · rintro ⟨R,k,hk⟩
    let x : CubicThetaCoreIndex r := ⟨(R.unit,R.order,
      ⟨(R.squarefreePart,R.cubePart),R.squarefree_primary,R.cube_primary,R.squarefree⟩),k,hk⟩
    exact ⟨x,Subtype.ext R.numerator_eq.symm⟩

lemma cubicThetaCoreFreeArgument_injective (r : Eisenstein) :
    Function.Injective (cubicThetaCoreFreeArgument r) := by
  intro x y he
  exact Prod.ext (cubicThetaCoreArgument_injective r (congrArg Prod.fst he))
    (Subtype.ext (congrArg Prod.snd he))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualFrequency
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion from the common theta lattice to the dual lattice.
The fixed dilation by 729 is retained in the transform argument. -/
noncomputable section
namespace CubicFirstMoment

lemma complexAngular_mul (ℓ : ℤ) (z w : ℂ) :
    complexAngular ℓ (z*w)=complexAngular ℓ z*complexAngular ℓ w := by
  simp only [complexAngular,norm_mul,Complex.ofReal_mul]
  rw [mul_div_mul_comm,mul_zpow]

lemma cubicThetaCircleOrder_neg (rev : Bool) (k : ℕ) :
    cubicThetaCircleOrder rev k = -cubicThetaCircleOrder (!rev) k := by
  cases rev <;> simp [cubicThetaCircleOrder]

lemma cubicTheta_dual_phase (ℓ : ℤ) (n : MetaplecticDualArgument) (d : Eisenstein) :
    theta ℓ (n.val*d^3)=theta ℓ lambdaE*
      complexAngular ℓ ((d:ℂ)^3*metaplecticFrequency n) := by
  have he : ((n.val*d^3:Eisenstein):ℂ)=
      (lambdaE:ℂ)*((d:ℂ)^3*metaplecticFrequency n) := by
    simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,metaplecticFrequency]
    change (n.val:ℂ)*(d:ℂ)^3=traceLambda*((d:ℂ)^3*((n.val:ℂ)/traceLambda))
    field_simp [traceLambda_ne_zero]
  rw [←complexAngular_coe,he,complexAngular_mul,complexAngular_coe]

lemma cubicTheta_dual_norm (n : MetaplecticDualArgument) :
    ‖cubicThetaFrequency n.val‖^2=Complex.normSq (metaplecticFrequency n)/27 := by
  rw [cubicThetaFrequency_sq,cubicTheta_metaplectic_normSq]
  ring

lemma cubicTheta_dual_cube_argument {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (d : Eisenstein) (X : ℝ) :
    cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2*norm d^3=
      (2*Real.pi)^4*Complex.normSq ((d:ℂ)^3*metaplecticFrequency n)*(X/729)/norm r^2 := by
  rw [cubicThetaVoronoi_dual_argument hr,Complex.normSq_mul,map_pow]
  change (2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/(729*norm r^2)*norm d^3=
    (2*Real.pi)^4*(norm d^3*Complex.normSq (metaplecticFrequency n))*(X/729)/norm r^2
  ring

lemma cubicThetaFreeLocalDualTerm_frequency {r : Eisenstein} (hr : primary r)
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    cubicThetaFreeLocalDualTerm r rev k W σ X x=
      27*theta (cubicThetaCircleOrder rev k) lambdaE*
        metaplecticDualTerm cubicThetaCoreCoefficient r (cubicThetaCircleOrder (!rev) k)
          W σ (X/729) (cubicThetaCoreFreeArgument r x) := by
  have he := congrArg Subtype.val (cubicThetaFreeCubeJoin_argument r x)
  change cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x)=
    cubicThetaCommonNumerator x.1.val*(x.2.val:Eisenstein)^3 at he
  unfold cubicThetaFreeLocalDualTerm
  rw [he,show cubicThetaCommonNumerator x.1.val=(cubicThetaCoreArgument x.1).val from rfl]
  change theta _ ((cubicThetaCoreArgument x.1).val*(x.2.val:Eisenstein)^3)*
    (cubicThetaCoreCoefficient r (cubicThetaCoreArgument x.1)*
      metaplecticLocalCoefficient r (cubicThetaCoreArgument x.1))/_*_= _
  rw [cubicTheta_dual_phase,
    cubicTheta_dual_cube_argument hr (cubicThetaCoreArgument x.1) (x.2.val:Eisenstein),
    cubicTheta_dual_norm (cubicThetaCoreArgument x.1)]
  dsimp only [metaplecticDualTerm,cubicThetaCoreFreeArgument]
  rw [ite_eq_left x.2.property]
  simp only [←cubicThetaCircleOrder_neg rev k,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full dual sum of the concrete core coefficient, with summability
transferred from the proved arithmetic free-cube parametrization. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaDualTerm_support (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    Function.support (metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X) ⊆
      Set.range (cubicThetaCoreFreeArgument r) := by
  intro nd hnd
  have hd : IsCoprime (nd.2:Eisenstein) r := by
    by_contra h
    exact hnd (by simp only [metaplecticDualTerm,ite_eq_right h])
  have hn : CubicThetaCoreSupport r nd.1 := by
    by_contra h
    exact hnd (by simp only [metaplecticDualTerm,ite_eq_left hd,
      cubicThetaCoreCoefficient,ite_eq_right h,zero_mul,zero_div])
  obtain ⟨x,hx⟩ := (cubicThetaCoreArgument_range r nd.1).mpr hn
  exact ⟨(x,⟨nd.2,hd⟩),Prod.ext hx rfl⟩

lemma cubicThetaDualTerm_tsum (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    (∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,
      metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X (cubicThetaCoreFreeArgument r x))=
    ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X nd :=
  (cubicThetaCoreFreeArgument_injective r).tsum_eq (cubicThetaDualTerm_support r ℓ W σ X)

lemma cubicThetaDualTerm_summable_iff (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    Summable (fun x : CubicThetaCoreIndex r × CubicThetaFreeArgument r =>
      metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X (cubicThetaCoreFreeArgument r x)) ↔
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X) :=
  (cubicThetaCoreFreeArgument_injective r).summable_iff
    (f:=metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X) (by
    intro nd hn
    by_contra hne
    exact hn (cubicThetaDualTerm_support r ℓ W σ X hne))

theorem cubicThetaFullDual_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r (cubicThetaCircleOrder (!rev) k)
      W σ (X/729)) ∧
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
    ((cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      (27*theta (cubicThetaCircleOrder rev k) lambdaE))*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r (cubicThetaCircleOrder (!rev) k)
          W σ (X/729) nd := by
  obtain ⟨hS,hE⟩ := cubicThetaFree_voronoi hr hs rev hk W hW hpos hsm hσ hX
  have hfactor : (27:ℂ)*theta (cubicThetaCircleOrder rev k) lambdaE≠0 :=
    mul_ne_zero (by norm_num) (norm_ne_zero_iff.mp (by
      rw [norm_theta (show lambdaE≠0 by
        intro h
        exact traceLambda_ne_zero (by simpa only [lambdaE_coe,ZeroMemClass.coe_zero] using congrArg (fun z : Eisenstein => (z:ℂ)) h))]
      norm_num))
  have he := cubicThetaFreeLocalDualTerm_frequency hr rev k W σ X
  have hSc := hS.congr he
  have hSr := (summable_mul_left_iff hfactor).mp hSc
  refine ⟨(cubicThetaDualTerm_summable_iff r _ W σ (X/729)).mp hSr,?_⟩
  rw [show (∑' x,cubicThetaFreeLocalDualTerm r rev k W σ X x)=
    (27*theta (cubicThetaCircleOrder rev k) lambdaE)*
      ∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,
        metaplecticDualTerm cubicThetaCoreCoefficient r (cubicThetaCircleOrder (!rev) k)
          W σ (X/729) (cubicThetaCoreFreeArgument r x) by
    simp only [he,tsum_mul_left],cubicThetaDualTerm_tsum] at hE
  simpa only [mul_assoc] using hE

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualPhase
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact angular phase of the constructed dual formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_theta_lambda (ℓ : ℤ) : theta ℓ lambdaE=Complex.I^ℓ := by
  have hnorm : ‖traceLambda‖=Real.sqrt 3 := by
    rw [traceLambda_eq,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold theta
  rw [lambdaE_coe,hnorm,traceLambda_eq]
  congr 1
  exact mul_div_cancel_left₀ Complex.I (Complex.ofReal_ne_zero.mpr (by positivity))

lemma cubicTheta_root_ratio {r : Eisenstein} (hr : primary r) (rev : Bool) (k : ℕ) :
    cubicThetaLevelAngularRoot r rev k=
      (-(star (r:ℂ)/(r:ℂ)))^(cubicThetaCircleOrder (!rev) k) := by
  have hz : (r:ℂ)≠0 := fun h => primary_ne_zero hr (Subtype.ext h)
  have hn : (norm r:ℂ)=(r:ℂ)*star (r:ℂ) := by
    simpa only [norm,Complex.star_def,Complex.normSq_eq_norm_sq,Complex.ofReal_pow] using (Complex.mul_conj' (r:ℂ)).symm
  have he : -(norm r:ℂ)/(r:ℂ)^2=-(star (r:ℂ)/(r:ℂ)) := by
    rw [hn]
    field_simp
  rw [cubicThetaLevelAngularRoot,he]
  cases rev
  · simp only [Bool.not_false,cubicThetaCircleMultiplier,ite_true, if_true,cubicThetaCircleOrder,
      star_neg,zpow_neg,zpow_natCast]
    rw [←inv_pow,inv_neg,inv_div]
    simp only [Complex.star_def,map_div₀,starRingEnd_self_apply]
  · simp only [Bool.not_true,cubicThetaCircleMultiplier,Bool.false_eq_true,ite_false, if_false,
      cubicThetaCircleOrder,zpow_natCast]

lemma cubicTheta_root_phase {r : Eisenstein} (hr : primary r) (rev : Bool) (k : ℕ) :
    (cubicThetaLevelAngularRoot r rev k)⁻¹*
      theta (cubicThetaCircleOrder rev k) lambdaE=
    theta (cubicThetaCircleOrder (!rev) k) lambdaE*
      (star (r:ℂ)/(r:ℂ))^(-cubicThetaCircleOrder (!rev) k) := by
  let ℓ := cubicThetaCircleOrder (!rev) k
  let q := star (r:ℂ)/(r:ℂ)
  have hq : q≠0 := div_ne_zero (star_ne_zero.mpr (by
    intro h
    exact primary_ne_zero hr (Subtype.ext h))) (by
      intro h
      exact primary_ne_zero hr (Subtype.ext h))
  have hI : -q*Complex.I=Complex.I⁻¹*q := by rw [Complex.inv_I]; ring
  have he : (-q)^ℓ*Complex.I^ℓ=Complex.I^(-ℓ)*q^ℓ := by
    rw [←mul_zpow,hI,mul_zpow,inv_zpow,←zpow_neg]
  rw [cubicTheta_root_ratio hr,cubicThetaCircleOrder_neg rev k,
    cubicTheta_theta_lambda,cubicTheta_theta_lambda]
  change ((-q)^ℓ)⁻¹*Complex.I^(-ℓ)=Complex.I^ℓ*q^(-ℓ)
  apply mul_right_cancel₀ (zpow_ne_zero ℓ hq)
  calc
    _ = ((-q)^ℓ)⁻¹*(Complex.I^(-ℓ)*q^ℓ) := by ring
    _ = ((-q)^ℓ)⁻¹*((-q)^ℓ*Complex.I^ℓ) := by rw [he]
    _ = Complex.I^ℓ := by
      rw [←mul_assoc,inv_mul_cancel₀ (zpow_ne_zero _ (neg_ne_zero.mpr hq)),one_mul]
    _ = _ := by rw [mul_assoc,zpow_neg,inv_mul_cancel₀ (zpow_ne_zero _ hq),mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualScalar
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical and Gauss factors in the constructed transform. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaDualPrefactor_eq {r : Eisenstein} (hr : primary r) :
    cubicThetaDualPrefactor r=(norm r:ℂ)/((2*Real.pi:ℝ):ℂ)^2 := by
  have hsq := cubicThetaLevelScale_square r
  have hR : (norm r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero (primary_ne_zero hr)).ne'
  unfold cubicThetaDualPrefactor
  rw [show (-2:ℂ)=((-2:ℤ):ℂ) by norm_num,Complex.cpow_intCast,
    Complex.cpow_intCast]
  simp only [zpow_neg,zpow_ofNat,←Complex.ofReal_pow,hsq,Complex.ofReal_inv,inv_inv]
  rw [div_eq_mul_inv]

lemma cubicThetaGauss_square {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    ((Real.sqrt (norm r):ℂ)*gauss r)*star ((Real.sqrt (norm r):ℂ)*gauss r)=(norm r:ℂ) := by
  rw [mul_assoc,gauss_mul_conj_unnormalized hr hs,←Complex.ofReal_mul]
  congr 1
  nlinarith [Real.sq_sqrt (norm_nonneg r)]

lemma cubicThetaDual_scalar {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (rev : Bool) (k : ℕ) :
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*(81*metaplecticRawPrefactor r (cubicThetaCircleOrder (!rev) k))=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      (27*theta (cubicThetaCircleOrder rev k) lambdaE) := by
  have hthree : (3:ℝ)^(7/2:ℝ)=3*(3:ℝ)^(5/2:ℝ) := by
    rw [show (7/2:ℝ)=1+5/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_one]
  have hphase := cubicTheta_root_phase hr rev k
  have hrearrange : (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      (27*theta (cubicThetaCircleOrder rev k) lambdaE)=
    (theta (cubicThetaCircleOrder (!rev) k) lambdaE*
      (star (r:ℂ)/(r:ℂ))^(-cubicThetaCircleOrder (!rev) k))*(27*cubicThetaDualPrefactor r) := by
    rw [←hphase]
    ring
  rw [hrearrange,cubicThetaDualPrefactor_eq hr]
  unfold metaplecticRawPrefactor
  calc
    _ = ((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE*
      (81*(norm r:ℂ))/((3^(7/2:ℝ)*(2*Real.pi)^2:ℝ):ℂ)*
        (star (r:ℂ)/(r:ℂ))^(-cubicThetaCircleOrder (!rev) k) := by
      rw [←cubicThetaGauss_square hr hs]
      ring
    _ = _ := by
      rw [hthree]
      push_cast
      field_simp
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRawVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved nonzero-angular raw formula, with the full dual index set
and the actual fixed scale. This is not an assertion of the differently
normalized published input. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubicTheta_nonzero_order {ℓ : ℤ} (hℓ : ℓ≠0) :
    ∃ (rev : Bool) (k : ℕ), 0<k ∧ cubicThetaCircleOrder (!rev) k=ℓ := by
  cases ℓ with
  | ofNat n =>
    refine ⟨true,n,Nat.pos_of_ne_zero (fun hn => hℓ (by simp [hn])),?_⟩
    simp [cubicThetaCircleOrder]
  | negSucc n =>
    refine ⟨false,n+1,by omega,?_⟩
    simp only [Bool.not_false,cubicThetaCircleOrder,ite_true, if_true,Nat.cast_add,Nat.cast_one]
    omega

theorem cubicTheta_raw_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] {ℓ : ℤ} (hℓ : ℓ≠0)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ (X/729)) ∧
    metaplecticRawCompleted r ℓ W X=
      81*metaplecticRawPrefactor r ℓ*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ (X/729) nd := by
  obtain ⟨rev,k,hk,rfl⟩ := cubicTheta_nonzero_order hℓ
  obtain ⟨hS,hE⟩ := cubicThetaFullDual_voronoi hr hs rev hk W hW hpos hsm hσ hX
  refine ⟨hS,?_⟩
  let A := (((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r)
  have hA : A≠0 := by
    dsimp only [A]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
      · rw [cubicTheta_theta_lambda]
        exact zpow_ne_zero _ Complex.I_ne_zero
    · apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
          (norm_pos_of_ne_zero (primary_ne_zero hr))).ne'
      · apply norm_ne_zero_iff.mp
        rw [norm_gauss_of_squarefree hr hs]
        norm_num
  apply mul_left_cancel₀ hA
  calc
    _ = _ := hE
    _ = _ := by rw [←cubicThetaDual_scalar hr hs rev k]; ring

theorem cubicTheta_completed_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    {ℓ : ℤ} (hℓ : ℓ≠0)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    metaplecticCompleted r ℓ W X=
      81*metaplecticPrefactor r ℓ*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ (X/729) nd := by
  let : Finite (Residues r) := finite_residues (primary_ne_zero hr)
  let : Fintype (Residues r) := Fintype.ofFinite _
  rw [metaplecticCompleted_eq_raw hr,(cubicTheta_raw_voronoi hr hs hℓ W hW hpos hsm hσ hX).2]
  calc
    _ = 81*(gauss r*theta ℓ r*metaplecticRawPrefactor r ℓ)*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ (X/729) nd := by ring
    _ = _ := by rw [metaplecticPrefactor_normalization hr hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLowPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary small-power absorption in the polynomial scale range. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_low_scale_power {Y R X B δ : ℝ}
    (hY : 1 ≤ Y) (hR : 0 < R) (hX : 0 < X) (_hB : 0 ≤ B) (hδ : 0 < δ)
    (hRY : R ≤ Y^B) (hYX : Y^(-B) ≤ X) :
    R^(3*δ)*X^(-δ) ≤ Y^(4*B*δ) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hRpow : R^(3*δ) ≤ Y^(3*B*δ) := by
    apply (Real.rpow_le_rpow hR.le hRY (by positivity)).trans_eq
    rw [←Real.rpow_mul hYp.le]
    congr 1
    ring
  have hXpow : X^(-δ) ≤ Y^(B*δ) := by
    apply (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hYp _) hYX (by linarith)).trans_eq
    rw [←Real.rpow_mul hYp.le]
    congr 1
    ring
  calc
    _ ≤ Y^(3*B*δ)*Y^(B*δ) := mul_le_mul hRpow hXpow
      (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [←Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompletedLow
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonzero-angular low-height bound. The fixed dilation and
numerical factor of the proved formula are absorbed in its constant. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicTheta_dilated_power {X : ℝ} (hX : 0<X) (σ : ℝ) :
    (X/729)^(-σ)=X^(-σ)*(729:ℝ)^σ := by
  rw [Real.div_rpow hX.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤729),
    div_eq_mul_inv,inv_inv]

theorem uniform_cubicTheta_completed_low
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W)
    {ℓ : ℤ} (hℓ : ℓ≠0) {ε σ : ℝ} (hε : 0<ε) (hσ : 0<σ) :
    ∃ K : ℝ, 0≤K ∧ ∀ i r, primary r → Squarefree r → ∀ X : ℝ, 0<X →
      ‖metaplecticCompleted r ℓ (W i) X‖≤
        K*Real.sqrt (norm r)*norm r^(ε+2*σ)*X^(-σ) := by
  have hGamma := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ)
    (-σ-1/6) (lt_of_lt_of_le (by norm_num : -(1/2:ℝ)<0) (metaplecticAngularShift_nonneg ℓ))
  obtain ⟨C,hC,hTr⟩ := hW.metaplecticTransform_bound ℓ hσ hGamma
  obtain ⟨M,hM,hMass⟩ := metaplectic_coefficient_mass_small_power
    cubicThetaCoreCoefficient_bounds hε hσ
  let S : ℝ := ∑' d : PrimaryArgument,norm d^(-5/2-3*σ)
  have hS : 0≤S := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  let P : ℝ := 3^(7/2:ℝ)*(2*Real.pi)^2
  have hP : 0<P := by dsimp [P]; positivity
  refine ⟨81*C*M*S*(2*Real.pi)^(-4*σ)*(729:ℝ)^σ/P,by positivity,?_⟩
  intro i r hr hsr X hX
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRs : norm r^(2*σ)*norm r^ε=norm r^(ε+2*σ) := by
    rw [←Real.rpow_add hR]
    congr 1
    ring
  have hbound := metaplecticDualTerm_tsum_norm_bound hr ℓ (W i) hσ
    (div_pos hX (by norm_num : (0:ℝ)<729)) hC (hTr i)
    (hMass r hr hsr).1 (hMass r hr hsr).2
  rw [cubicTheta_completed_voronoi hr hsr hℓ (W i) (hW.compact i)
    (hW.positive i) (hW.smooth i) hσ hX,norm_mul,norm_mul,
    norm_metaplecticPrefactor (primary_ne_zero hr),Complex.norm_ofNat]
  calc
    _ ≤ (81*(Real.sqrt (norm r)/P))*
        ((C*((2*Real.pi)^(-4*σ)*(X/729)^(-σ)*norm r^(2*σ)))*(M*norm r^ε)*S) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (81*C*M*S*(2*Real.pi)^(-4*σ)*(729:ℝ)^σ/P)*Real.sqrt (norm r)*
        (norm r^(2*σ)*norm r^ε)*X^(-σ) := by rw [cubicTheta_dilated_power hX]; ring
    _ = _ := by rw [hRs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialDual
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial dual sum uses the same proved local support and free-cube
reindexing as the angular formula. Its separate actual pole is retained. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem cubicThetaFullDual_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729)) ∧
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))*
      metaplecticRawCompleted r 0 W X=
      (cubicThetaDualPrefactor r*27)*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd+
      cubicThetaResidueRadialPole r*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ) := by
  obtain ⟨hS,hE⟩ := cubicThetaResidue_radial_voronoi hr hs W hW hpos hsm hσ hX
  rw [cubicThetaResidueDualTerm_local hr hs] at hS hE
  have hI := hS.comp_injective cubicThetaCommonArgument_injective
  have hJ := hI.comp_injective (cubicThetaFreeCubeJoin_injective (primary_ne_zero hr))
  have he := cubicThetaFreeLocalDualTerm_eq hr false 0 W σ X
  have hfree := hJ.congr he
  rw [cubicThetaLocalDualTerm_reindex,cubicTheta_free_cube_tsum (primary_ne_zero hr)] at hE
  simp only [he] at hE
  have hf (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
      cubicThetaFreeLocalDualTerm r false 0 W σ X x=
        27*metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729)
          (cubicThetaCoreFreeArgument r x) := by
    simpa only [cubicThetaCircleOrder,Bool.not_false,Bool.false_eq_true,ite_true, if_true,ite_false, if_false,
      Nat.cast_zero,neg_zero,theta_zero,mul_one] using
      cubicThetaFreeLocalDualTerm_frequency hr false 0 W σ X x
  have hprod := hfree.congr hf
  have hsmall := (summable_mul_left_iff (by norm_num : (27:ℂ)≠0)).mp hprod
  refine ⟨(cubicThetaDualTerm_summable_iff r 0 W σ (X/729)).mp hsmall,?_⟩
  simp only [hf,tsum_mul_left,cubicThetaDualTerm_tsum,mul_assoc] at hE
  simpa only [mul_assoc] using hE

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialRawVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radial raw/completed Voronoi identities. The main term remains
in terms of the computed residue, without asserting its normalization. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubicThetaRadialGauss_ne_zero {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    gauss r≠0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_gauss_of_squarefree hr hs]
  norm_num

lemma cubicThetaRadialRawScalar_ne_zero {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))≠0 := by
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (norm_pos_of_ne_zero (primary_ne_zero hr))).ne') (cubicThetaRadialGauss_ne_zero hr hs)

theorem cubicTheta_raw_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729)) ∧
    metaplecticRawCompleted r 0 W X=
      81*metaplecticRawPrefactor r 0*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd+
      cubicThetaActualRawRadialMain r W X := by
  obtain ⟨hS,hE⟩ := cubicThetaFullDual_radial_voronoi hr hs W hW hpos hsm hσ hX
  refine ⟨hS,?_⟩
  let A := ((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r)
  have hA : A≠0 := cubicThetaRadialRawScalar_ne_zero hr hs
  have hscalar : A*(81*metaplecticRawPrefactor r 0)=cubicThetaDualPrefactor r*27 := by
    simpa only [A,cubicThetaCircleOrder,Bool.not_false,Bool.false_eq_true,ite_true, if_true,ite_false, if_false,
      Nat.cast_zero,neg_zero,theta_zero,mul_one,cubicThetaLevelAngularRoot,pow_zero,
      inv_one,one_mul] using cubicThetaDual_scalar hr hs false 0
  have hp : A*cubicThetaActualRawRadialMain r W X=
      cubicThetaResidueRadialPole r*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ) := by
    change A*(cubicThetaResidueRadialPole r/A*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ))=_
    field_simp
  apply mul_left_cancel₀ hA
  rw [mul_add,←mul_assoc,hscalar,hp]
  exact hE

lemma cubicTheta_radial_main_completed {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (W : ℝ→ℂ) (X : ℝ) :
    gauss r*cubicThetaActualRawRadialMain r W X=cubicThetaActualCompletedRadialMain r W X := by
  have hg := cubicThetaRadialGauss_ne_zero hr hs
  have hthree : ((3^(5/2:ℝ):ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hsqrt : (Real.sqrt (norm r):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hr))).ne'
  unfold cubicThetaActualRawRadialMain cubicThetaActualCompletedRadialMain
  field_simp

theorem cubicTheta_completed_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W⊆Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    metaplecticCompleted r 0 W X=
      81*metaplecticPrefactor r 0*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd+
      cubicThetaActualCompletedRadialMain r W X := by
  let : Finite (Residues r) := finite_residues (primary_ne_zero hr)
  let : Fintype (Residues r) := Fintype.ofFinite _
  rw [metaplecticCompleted_eq_raw hr,(cubicTheta_raw_radial_voronoi hr hs W hW hpos hsm hσ hX).2,
    theta_zero,mul_one,mul_add,cubicTheta_radial_main_completed hr hs]
  congr 1
  calc
    _ = 81*(gauss r*theta 0 r*metaplecticRawPrefactor r 0)*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd := by rw [theta_zero]; ring
    _ = _ := by rw [metaplecticPrefactor_normalization hr hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialLow
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform low-height bounds after subtracting the actual radial residue.
The normalization of that residue is not needed for this remainder bound. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem uniform_cubicTheta_radial_remainder_low
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W)
    {ε σ : ℝ} (hε : 0<ε) (hσ : 0<σ) :
    ∃ K : ℝ, 0≤K ∧ ∀ i r, primary r → Squarefree r → ∀ X : ℝ, 0<X →
      ‖metaplecticCompleted r 0 (W i) X-cubicThetaActualCompletedRadialMain r (W i) X‖≤
        K*Real.sqrt (norm r)*norm r^(ε+2*σ)*X^(-σ) := by
  have hGamma := angularGammaQuotientStripBound_proved (metaplecticAngularShift 0)
    (-σ-1/6) (lt_of_lt_of_le (by norm_num : -(1/2:ℝ)<0) (metaplecticAngularShift_nonneg 0))
  obtain ⟨C,hC,hTr⟩ := hW.metaplecticTransform_bound 0 hσ hGamma
  obtain ⟨M,hM,hMass⟩ := metaplectic_coefficient_mass_small_power
    cubicThetaCoreCoefficient_bounds hε hσ
  let S : ℝ := ∑' d : PrimaryArgument,norm d^(-5/2-3*σ)
  have hS : 0≤S := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  let P : ℝ := 3^(7/2:ℝ)*(2*Real.pi)^2
  have hP : 0<P := by dsimp [P]; positivity
  refine ⟨81*C*M*S*(2*Real.pi)^(-4*σ)*(729:ℝ)^σ/P,by positivity,?_⟩
  intro i r hr hsr X hX
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRs : norm r^(2*σ)*norm r^ε=norm r^(ε+2*σ) := by
    rw [←Real.rpow_add hR]
    congr 1
    ring
  have hbound := metaplecticDualTerm_tsum_norm_bound hr 0 (W i) hσ
    (div_pos hX (by norm_num : (0:ℝ)<729)) hC (hTr i)
    (hMass r hr hsr).1 (hMass r hr hsr).2
  rw [cubicTheta_completed_radial_voronoi hr hsr (W i) (hW.compact i)
    (hW.positive i) (hW.smooth i) hσ hX,add_sub_cancel_right,norm_mul,norm_mul,
    norm_metaplecticPrefactor (primary_ne_zero hr),Complex.norm_ofNat]
  calc
    _ ≤ (81*(Real.sqrt (norm r)/P))*
        ((C*((2*Real.pi)^(-4*σ)*(X/729)^(-σ)*norm r^(2*σ)))*(M*norm r^ε)*S) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (81*C*M*S*(2*Real.pi)^(-4*σ)*(729:ℝ)^σ/P)*Real.sqrt (norm r)*
        (norm r^(2*σ)*norm r^ε)*X^(-σ) := by rw [cubicTheta_dilated_power hX]; ring
    _ = _ := by rw [hRs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCenteredLow
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centering the actual completed transform with its now determined
radial constant, at every fixed angular mode. -/
noncomputable section
namespace CubicFirstMoment

theorem uniform_cubicTheta_centered_low
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) {ε σ : ℝ} (hε : 0<ε) (hσ : 0<σ) :
    ∃ K : ℝ, 0≤K ∧ ∀ i r, primary r → Squarefree r → ∀ X : ℝ, 0<X →
      ‖metaplecticCompleted r ℓ (W i) X-metaplecticMain r ℓ (W i) X‖≤
        K*Real.sqrt (norm r)*norm r^(ε+2*σ)*X^(-σ) := by
  by_cases hℓ : ℓ=0
  · subst ℓ
    obtain ⟨K,hK,h⟩ := uniform_cubicTheta_radial_remainder_low hW hε hσ
    refine ⟨K,hK,?_⟩
    intro i r hr hs X hX
    simpa only [cubicThetaActualCompletedRadialMain_eq hr (W i) hX] using h i r hr hs X hX
  · obtain ⟨K,hK,h⟩ := uniform_cubicTheta_completed_low hW hℓ hε hσ
    refine ⟨K,hK,?_⟩
    intro i r hr hs X hX
    simpa only [metaplecticMain,ite_eq_right hℓ,sub_zero] using h i r hr hs X hX

theorem uniform_cubicTheta_centered_subpower
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) {ε B : ℝ} (hε : 0<ε) (hB : 0≤B) :
    ∃ K : ℝ, 0≤K ∧ ∀ i r, primary r → Squarefree r →
      ∀ Y X : ℝ, 1≤Y → 0<X → norm r≤Y^B → Y^(-B)≤X →
        ‖metaplecticCompleted r ℓ (W i) X-metaplecticMain r ℓ (W i) X‖≤K*Y^ε*Real.sqrt (norm r) := by
  let δ := ε/(4*(B+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδε : 4*B*δ≤ε := by
    have hh : δ*(4*(B+1))=ε := by dsimp [δ]; field_simp
    nlinarith
  obtain ⟨K,hK,hbound⟩ := uniform_cubicTheta_centered_low hW ℓ hδ hδ
  refine ⟨K,hK,?_⟩
  intro i r hr hsr Y X hY hX hRY hYX
  have hs := metaplectic_low_scale_power hY (norm_pos_of_ne_zero (primary_ne_zero hr)) hX hB hδ hRY hYX
  have he : δ+2*δ=3*δ := by ring
  have hpow := Real.rpow_le_rpow_of_exponent_le hY hδε
  calc
    _ ≤ K*Real.sqrt (norm r)*norm r^(3*δ)*X^(-δ) := by simpa only [he] using hbound i r hr hsr X hX
    _ = (K*Real.sqrt (norm r))*(norm r^(3*δ)*X^(-δ)) := by ring
    _ ≤ (K*Real.sqrt (norm r))*Y^(4*B*δ) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (K*Real.sqrt (norm r))*Y^ε := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inversion of the cubic completion kernel. The Euler variable
for a prime ideal is first weighted, then replaced by its cube. Thus the
series identities below retain the actual cube-divisor support; they are
not ordinary (uncubed) convolution identities. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubeInverseCompletionSeries_coeff (x : EisensteinIdealPrime → ℂ)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff (3 • ν) (cubeInverseCompletionSeries x) =
      ν.prod (fun p k => x p^k)*((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ) := by
  rw [cubeInverseCompletionSeries,MvPowerSeries.coeff_expand_smul,
    MvPowerSeries.coeff_rescale,MvPowerSeries.coeff_map]
  rfl

private lemma primary_nat_pow {a : Eisenstein} (ha : primary a) (k : ℕ) :
    primary (a^k) := by
  induction k with
  | zero => simp [primary]
  | succ k ih => simpa only [pow_succ] using primary_mul ih ha

lemma idealPrimaryGenerator_eq_normalized_prime_product {a : Eisenstein}
    (ha : primary a) {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a) :
    idealPrimaryGenerator ν =
      ν.prod (fun p k => primaryNormalize (idealPrimeRepresentative p)^k) := by
  have hpp (p : EisensteinIdealPrime) (hp : p ∈ ν.support) :
      primary (primaryNormalize (idealPrimeRepresentative p)) := by
    apply primaryNormalize_primary
    apply unit_residue_of_dvd_primary ha
    apply (idealPrime_dvd_iff (primary_ne_zero ha) p).mpr
    have hpos : 0 < ν p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    exact hpos.trans_le (hν p)
  have hp : primary (ν.prod (fun p k => primaryNormalize (idealPrimeRepresentative p)^k)) :=
    primary_finset_prod _ _ (fun p hp => primary_nat_pow (hpp p hp) _)
  apply primary_associated_eq (idealPrimaryGenerator_primary ha hν) hp
  apply (primaryNormalize_associated _).symm.trans
  unfold idealExponentGenerator
  exact Associated.prod _ _ _ (fun p _ => Associated.pow_pow (n := ν p)
    (primaryNormalize_associated (idealPrimeRepresentative p)))

lemma normalized_prime_product_character {a : Eisenstein} (ha : primary a)
    {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a)
    (χ : Eisenstein → ℂ) (h1 : χ 1 = 1)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y) :
    ν.prod (fun p k => (χ (primaryNormalize (idealPrimeRepresentative p)))^k) =
      χ (idealPrimaryGenerator ν) := by
  rw [idealPrimaryGenerator_eq_normalized_prime_product ha hν]
  have hp (p : EisensteinIdealPrime) (hpm : p ∈ ν.support) :
      primary (primaryNormalize (idealPrimeRepresentative p)) := by
    apply primaryNormalize_primary
    apply unit_residue_of_dvd_primary ha
    apply (idealPrime_dvd_iff (primary_ne_zero ha) p).mpr
    exact (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpm)).trans_le (hν p)
  have hpow (b : Eisenstein) (hb : primary b) (k : ℕ) : χ (b^k) = (χ b)^k := by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ,hχ _ _ (primary_nat_pow hb k) hb,ih,pow_succ]
  change (∏ p ∈ ν.support, χ (primaryNormalize (idealPrimeRepresentative p))^ν p) =
    χ (∏ p ∈ ν.support, primaryNormalize (idealPrimeRepresentative p)^ν p)
  suffices hfin : ∀ S : Finset EisensteinIdealPrime,
      (∀ p ∈ S, primary (primaryNormalize (idealPrimeRepresentative p))) →
      (∏ p ∈ S, χ (primaryNormalize (idealPrimeRepresentative p))^ν p) =
        χ (∏ p ∈ S, primaryNormalize (idealPrimeRepresentative p)^ν p) from hfin _ hp
  intro S hS
  induction S using Finset.induction_on with
  | empty => simpa using h1.symm
  | @insert p S hps ih =>
    have hp' := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, primary (primaryNormalize (idealPrimeRepresentative q)) :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps,Finset.prod_insert hps,
      hχ _ _ (primary_nat_pow hp' _) (primary_finset_prod S _
        (fun q hq => primary_nat_pow (hS' q hq) _)),hpow _ hp']
    congr 1
    exact ih hS'

lemma metaplecticCompletionWeight_mul (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {a b : Eisenstein} (_ha : primary a) (_hb : primary b) :
    metaplecticCompletionWeight r ℓ t (a*b) =
      metaplecticCompletionWeight r ℓ t a*metaplecticCompletionWeight r ℓ t b := by
  unfold metaplecticCompletionWeight
  rw [IsCoprime.mul_left_iff]
  by_cases har : IsCoprime a r
  · by_cases hbr : IsCoprime b r
    · simp only [har,hbr,and_self,ite_true, if_true,norm_mul_eq,theta_mul,
        Real.sqrt_mul (norm_nonneg a),Complex.ofReal_mul]
      rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg a) (norm_nonneg b)]
      ring
    · simp [har,hbr]
  · simp [har]

/-- At a primary principal ideal the expanded inverse kernel has
exactly the arithmetic weight `mu(c)|c| theta_(3ell)(c)(Nc)^(3it)`.
There is no assumption that `c` is squarefree. -/
theorem cubeInverseCompletionSeries_at_primary (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    MvPowerSeries.coeff (3 • idealExponentOf c)
      (cubeInverseCompletionSeries (fun p => metaplecticCompletionWeight r ℓ t
        (primaryNormalize (idealPrimeRepresentative p)))) =
      (idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c := by
  rw [cubeInverseCompletionSeries_coeff,normalized_prime_product_character hc le_rfl
    (metaplecticCompletionWeight r ℓ t) (metaplecticCompletionWeight_one r ℓ t)
    (fun _ _ ha hb => metaplecticCompletionWeight_mul r ℓ t ha hb),
    idealPrimaryGenerator_at_element hc,idealMoebiusSeries_at_element (primary_ne_zero hc)]
  push_cast
  ring

lemma norm_metaplecticCompletionWeight {c : Eisenstein} (hc : primary c)
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) :
    ‖metaplecticCompletionWeight r ℓ t c‖ =
      if IsCoprime c r then Real.sqrt (norm c) else 0 := by
  unfold metaplecticCompletionWeight
  split_ifs
  · rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),norm_theta (primary_ne_zero hc),mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero (primary_ne_zero hc))]
    simp
  · exact norm_zero

theorem norm_cubeInverseCompletionSeries_at_primary
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) {c : Eisenstein} (hc : primary c) :
    ‖MvPowerSeries.coeff (3 • idealExponentOf c)
      (cubeInverseCompletionSeries (fun p => metaplecticCompletionWeight r ℓ t
        (primaryNormalize (idealPrimeRepresentative p))))‖ ≤ Real.sqrt (norm c) := by
  rw [cubeInverseCompletionSeries_at_primary r ℓ t hc,norm_mul]
  have hmu : ‖(idealMoebius c:ℂ)‖ ≤ 1 := by
    have h := idealMoebiusSeries_abs_le_one (idealExponentOf c)
    rw [idealMoebiusSeries_at_element (primary_ne_zero hc)] at h
    have he : (idealMoebius c:ℂ) = ((idealMoebius c:ℝ):ℂ) := by norm_cast
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    exact h
  have hw : ‖metaplecticCompletionWeight r ℓ t c‖ ≤ Real.sqrt (norm c) := by
    rw [norm_metaplecticCompletionWeight hc]
    split_ifs
    · rfl
    · exact Real.sqrt_nonneg _
  exact (mul_le_mul_of_nonneg_right hmu (_root_.norm_nonneg _)).trans (by simpa using hw)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticInverseScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact amplitude and polynomial length range after angular
inverse completion. Each cube divisor contributes one inverse norm. -/
noncomputable section
namespace CubicFirstMoment

lemma norm_metaplectic_inverse_weight (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    ‖(idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c‖ ≤ Real.sqrt (norm c) := by
  have h := norm_cubeInverseCompletionSeries_at_primary r ℓ t hc
  rwa [cubeInverseCompletionSeries_at_primary r ℓ t hc] at h

lemma metaplectic_inverse_length_range {Y U N B : ℝ}
    (hY : 1 ≤ Y) (hB : 0 ≤ B) (hUlo : Y^(-B) ≤ U) (hUhi : U ≤ Y^B)
    (hNlo : 1 ≤ N) (hNhi : N ≤ Y^B) :
    0 < U/N^3 ∧ Y^(-(4*B)) ≤ U/N^3 ∧ U/N^3 ≤ Y^(4*B) := by
  have hYp := zero_lt_one.trans_le hY
  have hUp := (Real.rpow_pos_of_pos hYp (-B)).trans_le hUlo
  have hNp := zero_lt_one.trans_le hNlo
  have hNcube : N^3 ≤ Y^(3*B) := by
    calc
      _ ≤ (Y^B)^3 := pow_le_pow_left₀ hNp.le hNhi 3
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hYp.le]; congr 1; ring
  refine ⟨div_pos hUp (pow_pos hNp 3),?_,?_⟩
  · apply (le_div_iff₀ (pow_pos hNp 3)).mpr
    calc
      _ ≤ Y^(-(4*B))*Y^(3*B) := mul_le_mul_of_nonneg_left hNcube (by positivity)
      _ = Y^(-B) := by rw [←Real.rpow_add hYp]; congr 1; ring
      _ ≤ U := hUlo
  · exact (div_le_self hUp.le (one_le_pow₀ hNlo)).trans
      (hUhi.trans (Real.rpow_le_rpow_of_exponent_le hY (by linarith)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShortInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short part of inverse completion. The same actual error sum
serves the radial and every fixed angular Type-I argument. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_sqrt_norm_mass {C : ℝ} (hC : 0 ≤ C) :
    (∑ c ∈ primaryElementBall C, Real.sqrt (norm c)) ≤ 18*C^(3/2:ℝ) := by
  have hsub : primaryElementBall C ⊆ nonzeroNormBall C := by
    intro c hc
    obtain ⟨hp,hn⟩ := mem_primaryElementBall.mp hc
    exact mem_nonzeroNormBall.mpr ⟨hn,primary_ne_zero hp⟩
  have hcard : ((primaryElementBall C).card:ℝ) ≤ 18*C :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hC)
  calc
    _ ≤ ∑ c ∈ primaryElementBall C, Real.sqrt C := Finset.sum_le_sum
      (fun c hc => Real.sqrt_le_sqrt (mem_primaryElementBall.mp hc).2)
    _ = ((primaryElementBall C).card:ℝ)*Real.sqrt C := by simp
    _ ≤ (18*C)*Real.sqrt C := mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _)
    _ = _ := by
      by_cases hz : C = 0
      · simp [hz]
      · have hp : 0 < C := lt_of_le_of_ne hC (Ne.symm hz)
        rw [Real.sqrt_eq_rpow,show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hp,
          Real.rpow_one]
        ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCenteredShortInverse
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual centered short inverse-completion bound, including the radial mode. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_centered_short_completion_error
    {ι : Type*} {W : ι → ℝ → ℂ} (hW : UniformLogWeights W) (ℓ : ℤ)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → Squarefree r →
      ∀ Y U C : ℝ, 1 ≤ Y → Y^(-B) ≤ U → U ≤ Y^B →
      0 ≤ C → C ≤ Y^B → norm r ≤ Y^B →
      ‖metaplecticShortCompletionError r ℓ (W i) U C‖ ≤
        K*Y^ε*Real.sqrt (norm r)*C^(3/2:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := uniform_cubicTheta_centered_subpower hW ℓ hε
    (show 0 ≤ 4*B by positivity)
  refine ⟨18*K,by positivity,?_⟩
  intro i r hr hsr Y U C hY hUlo hUhi hC hChi hrhi
  have hrbig : norm r ≤ Y^(4*B) := hrhi.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by linarith))
  have hc (c : Eisenstein) (hc : c ∈ primaryElementBall C) :
      ‖((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
        (metaplecticCompleted r ℓ (W i) (U/norm c^3)-
          metaplecticMain r ℓ (W i) (U/norm c^3))‖ ≤
          Real.sqrt (norm c)*(K*Y^ε*Real.sqrt (norm r)) := by
    obtain ⟨hcp,hcn⟩ := mem_primaryElementBall.mp hc
    obtain ⟨hpos,hlo,_⟩ := metaplectic_inverse_length_range hY hB hUlo hUhi
      (one_le_norm (primary_ne_zero hcp)) (hcn.trans hChi)
    rw [norm_mul]
    exact mul_le_mul (norm_metaplectic_inverse_weight r ℓ 0 hcp)
      (hbound i r hr hsr Y _ hY hpos hrbig hlo) (_root_.norm_nonneg _) (Real.sqrt_nonneg _)
  unfold metaplecticShortCompletionError
  calc
    _ ≤ ∑ c ∈ primaryElementBall C,
        Real.sqrt (norm c)*(K*Y^ε*Real.sqrt (norm r)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hc)
    _ = (∑ c ∈ primaryElementBall C, Real.sqrt (norm c))*(K*Y^ε*Real.sqrt (norm r)) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (18*C^(3/2:ℝ))*(K*Y^ε*Real.sqrt (norm r)) :=
      mul_le_mul_of_nonneg_right (primary_sqrt_norm_mass hC) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShortLogInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short inverse-completion error for the original logarithmically
varying weights, in both the radial and fixed angular modes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticCompleted_const_mul (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U : ℝ) (z : ℂ) :
    metaplecticCompleted r ℓ (fun x => z*W x) U = z*metaplecticCompleted r ℓ W U := by
  unfold metaplecticCompleted
  rw [←tsum_mul_left]
  apply tsum_congr
  intro du
  by_cases hc : IsCoprime (du.1:Eisenstein) r
  · simp only [hc,ite_true, if_true]
    ring
  · simp only [hc,ite_false, if_false,mul_zero]

lemma metaplecticMain_const_mul (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U : ℝ) (z : ℂ) :
    metaplecticMain r ℓ (fun x => z*W x) U = z*metaplecticMain r ℓ W U := by
  have hm : mellin (fun x => z*W x) (5/6) = z*mellin W (5/6) := by
    simpa only [smul_eq_mul] using mellin_const_smul W (5/6) z
  unfold metaplecticMain
  split_ifs
  · rw [hm]
    ring
  · exact (mul_zero _).symm

lemma metaplecticShortCompletionError_const_mul (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (U C : ℝ) (z : ℂ) :
    metaplecticShortCompletionError r ℓ (fun x => z*W x) U C =
      z*metaplecticShortCompletionError r ℓ W U C := by
  unfold metaplecticShortCompletionError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [metaplecticCompleted_const_mul,metaplecticMain_const_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCenteredShortLogInverse
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered short completion bound for logarithmic weights. -/
noncomputable section
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.cubicTheta_centered_short_completion_error
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W) (ℓ : ℤ)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → Squarefree r →
      ∀ U C : ℝ, (Y i)^(-B) ≤ U → U ≤ (Y i)^B →
      0 ≤ C → C ≤ (Y i)^B → norm r ≤ (Y i)^B →
      ‖metaplecticShortCompletionError r ℓ (W i) U C‖ ≤
        K*(Y i)^ε*Real.sqrt (norm r)*C^(3/2:ℝ) := by
  have hs : 0 < ε/2 := half_pos hε
  obtain ⟨K,hK,hbound⟩ := (hW.normalize hs).cubicTheta_centered_short_completion_error ℓ hs hB
  refine ⟨K,hK,?_⟩
  intro i r hr hsr U C hUlo hUhi hC hChi hrhi
  have hY : 0 < Y i := zero_lt_one.trans_le (hW.length_one i)
  have he : metaplecticShortCompletionError r ℓ (normalizedLogWeight Y W (ε/2) i) U C =
      (((Y i)^(-(ε/2)):ℝ):ℂ)*metaplecticShortCompletionError r ℓ (W i) U C := by
    change metaplecticShortCompletionError r ℓ (fun x => ((Y i)^(-(ε/2)):ℝ) • W i x) U C = _
    simp_rw [Complex.real_smul]
    exact metaplecticShortCompletionError_const_mul r ℓ (W i) U C _
  have hb := hbound i r hr hsr (Y i) U C (hW.length_one i) hUlo hUhi hC hChi hrhi
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hY.le _)] at hb
  have hp : (Y i)^(ε/2)*(Y i)^(-(ε/2)) = 1 := by
    rw [←Real.rpow_add hY,add_neg_cancel,Real.rpow_zero]
  calc
    _ = (Y i)^(ε/2)*((Y i)^(-(ε/2))*‖metaplecticShortCompletionError r ℓ (W i) U C‖) := by
      rw [←mul_assoc,hp,one_mul]
    _ ≤ (Y i)^(ε/2)*(K*(Y i)^(ε/2)*Real.sqrt (norm r)*C^(3/2:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)
    _ = K*((Y i)^(ε/2)*(Y i)^(ε/2))*Real.sqrt (norm r)*C^(3/2:ℝ) := by ring
    _ = _ := by rw [←Real.rpow_add hY,show ε/2+ε/2 = ε by ring]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCenteredSelectedOuter
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered actual theta formula supplies this estimate for every fixed mode. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.cubicTheta_centered_selected_short
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X N U C : ℝ),
      1 ≤ X → 0 ≤ N → 0 ≤ C →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ norm r ≤ N) →
      (∀ r ∈ S, Y (w r) ≤ X ∧ (Y (w r))^(-b) ≤ U ∧ U ≤ (Y (w r))^b ∧
        C ≤ (Y (w r))^b ∧ norm r ≤ (Y (w r))^b) →
      ‖∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C‖ ≤
        K*X^ε*Real.sqrt N*C^(3/2:ℝ)*(∑ r ∈ S, ‖α r‖) := by
  obtain ⟨K,hK,hbound⟩ := hW.cubicTheta_centered_short_completion_error ℓ hε hb
  refine ⟨K,hK,?_⟩
  intro w S α X N U C _hX _hN hC hS hY
  have hbnd (r : Eisenstein) (hr : r ∈ S) :
      ‖metaplecticShortCompletionError r ℓ (W (w r)) U C‖ ≤
        K*X^ε*Real.sqrt N*C^(3/2:ℝ) := by
    obtain ⟨hp,hs,hn⟩ := hS r hr
    obtain ⟨hYX,hlo,hhi,hCY,hrY⟩ := hY r hr
    apply (hbound (w r) r hp hs U C hlo hhi hC hCY hrY).trans
    have hy := Real.rpow_le_rpow (zero_lt_one.trans_le (hW.length_one (w r))).le hYX hε.le
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hC _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hy hK) (Real.sqrt_le_sqrt hn)
      (Real.sqrt_nonneg _) (by positivity)
  calc
    _ ≤ ∑ r ∈ S, ‖α r‖*‖metaplecticShortCompletionError r ℓ (W (w r)) U C‖ := by
      simpa only [norm_mul] using norm_sum_le S
        (fun r => α r*metaplecticShortCompletionError r ℓ (W (w r)) U C)
    _ ≤ ∑ r ∈ S, ‖α r‖*(K*X^ε*Real.sqrt N*C^(3/2:ℝ)) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hbnd r hr) (_root_.norm_nonneg _))
    _ = _ := by rw [←Finset.sum_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShortOuter
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual short inverse-completion error after summing the level
coefficients. This is the common radial/angular short-error term. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma short_completion_level_scale {R : ℝ} (hR : 0 < R) :
    R*Real.sqrt (2*R) = Real.sqrt 2*R^(3/2:ℝ) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  simp_rw [Real.sqrt_eq_rpow]
  rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hR,Real.rpow_one]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCenteredShortModelLow
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered actual theta formula supplies this estimate for every fixed mode. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.cubicTheta_centered_short_low_power_oai
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U C : ℝ),
      2 ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → 0 ≤ C → C ≤ X →
      R^(3/2:ℝ)*C^(3/2:ℝ) ≤ X^(159/200:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
      ‖∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C‖ ≤
        K*X^(41/50:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := hW.cubicTheta_centered_selected_short ℓ
    (by norm_num : 0 < κ) (by norm_num : (0:ℝ) ≤ 2)
  refine ⟨K*D*Real.sqrt 2,by positivity,?_⟩
  intro w S α X R U C hX hR hU hRU hC hCX hscale hS hY hmass
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right hRp.le hU
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left (by linarith) hR
  have hXsq : X ≤ X^2 := by nlinarith
  have hXX : 2*X ≤ X^2 := by nlinarith [mul_nonneg hXp.le (show 0 ≤ X-2 by linarith)]
  have hNr : 2*R ≤ X^2 := (by linarith : 2*R ≤ 2*X).trans hXX
  have hlow : X^(-(2:ℝ)) ≤ U := by
    exact (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : -(2:ℝ) ≤ 0)).trans
      (by simpa only [Real.rpow_zero] using hU)
  have hb := hbound w S α X (2*R) U C hX1 (by positivity) hC hS (by
    intro r hr
    rw [hY r hr]
    exact ⟨le_rfl,hlow,by simpa only [Real.rpow_two] using hUX.trans hXsq,
      by simpa only [Real.rpow_two] using hCX.trans hXsq,
      by simpa only [Real.rpow_two] using (hS r hr).2.2.trans hNr⟩)
  apply hb.trans
  calc
    _ ≤ K*X^κ*Real.sqrt (2*R)*C^(3/2:ℝ)*(D*R*X^κ) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (K*D)*((X^κ*X^κ)*(R*Real.sqrt (2*R))*C^(3/2:ℝ)) := by ring
    _ = (K*D*Real.sqrt 2)*X^(2*κ)*(R^(3/2:ℝ)*C^(3/2:ℝ)) := by
      rw [short_completion_level_scale hRp,←Real.rpow_add hXp]
      have he : κ+κ = 2*κ := by ring
      rw [he]
      ring
    _ ≤ (K*D*Real.sqrt 2)*X^(2*κ)*X^(159/200:ℝ) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (K*D*Real.sqrt 2)*X^(2*κ+159/200) := by rw [Real.rpow_add hXp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_centered_short_low_power_oai.{u_1} := @OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_centered_short_low_power_oai.{u_1}
