-- Prove2me | solution 1 for OAI.CubicFirstMoment.primitiveAngularHeckeInput_proved
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:50:22.366275+00:00
-- url     : https://prove2.me/submissions/8e007373-5d43-4a26-887f-4a6ad1c0b113

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue character as an actual complete ideal character,
and exact restoration of Euler factors after primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ν : EisensteinIdealExponent) :
    ‖residueIdealChar q χ ν‖ ≤ 1 := residueChar_norm_le_one hq χ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueThetaLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete Eisenstein theta sum, including its zero term, equals the
ideal theta sum with its exact unit multiplicity. -/
noncomputable section
namespace CubicFirstMoment

lemma residue_nontrivial_of_nonprincipal {q : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (hn : χ ≠ 1) : Nontrivial (Residues q) := by
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hn
  apply nontrivial_of_ne (u : Residues q) 1
  intro he
  apply hu
  rw [he,map_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularConductorPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unit phase introduced by a harmonic Gaussian at the self-dual
Eisenstein conductor scale. -/
noncomputable section
namespace CubicFirstMoment

lemma conductor_abs (q : Eisenstein) :
    ‖(q:ℂ)*traceLambda‖ = 2*Real.pi*residueHeckeScale q := by
  have he : ‖(q:ℂ)*traceLambda‖^2 = 3*norm q := by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_mul,traceLambda_normSq]
    change norm q*3 = _
    ring
  have hs := residueHeckeScale_squared q
  have hA : 0 ≤ residueHeckeScale q := by unfold residueHeckeScale; positivity
  apply (sq_eq_sq₀ (_root_.norm_nonneg ((q:ℂ)*traceLambda)) (by positivity)).mp
  calc
    _ = 3*norm q := he
    _ = 4*Real.pi^2*(residueHeckeScale q)^2 := hs.symm
    _ = _ := by ring

lemma angularConductorPhase_norm {q : Eisenstein} (hq : q ≠ 0) :
    ‖angularConductorPhase q‖ = 1 := by
  have hA := residueHeckeScale_pos hq
  have hn : ‖(2:ℂ)‖ = 2 := by norm_num
  unfold angularConductorPhase
  rw [norm_div,norm_mul,norm_mul,norm_mul,norm_neg,hn,
    Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_of_nonneg hA.le,norm_star,conductor_abs]
  exact div_self (by positivity)

lemma angularConductorPhaseNeg_norm {q : Eisenstein} (hq : q ≠ 0) :
    ‖angularConductorPhaseNeg q‖ = 1 := by
  have he : ‖angularConductorPhaseNeg q‖ = ‖angularConductorPhase q‖ := by
    simp only [angularConductorPhaseNeg,angularConductorPhase,norm_div,norm_star]
  rw [he,angularConductorPhase_norm hq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite factor at 3 required by a fixed angular Hecke character.
The archimedean phase is retained separately, including after primitive
conductor reduction. Complete ideal sums therefore include every prime
at which the primitive character is unramified. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma star_theta {x : Eisenstein} (hx : x ≠ 0) (ℓ : ℤ) :
    star (theta ℓ x) = theta (-ℓ) x := by
  rw [show theta (-ℓ) x = (theta ℓ x)⁻¹ by simp only [theta, zpow_neg]]
  exact (Complex.inv_eq_conj (norm_theta hx ℓ)).symm

lemma angularResidueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    ‖angularResidueIdealChar q χ ℓ ν‖ ≤ 1 := by
  rw [angularResidueIdealChar, norm_mul, norm_theta (idealExponentGenerator_ne_zero ν), mul_one]
  exact residueIdealChar_norm_le_one hq χ ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealHeatMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gamma(s+kappa) factor obtained from the actual normalized angular
heat kernel; all positive ideals remain in the Dirichlet series. -/
noncomputable section
namespace CubicFirstMoment

lemma idealHeatTheta_one_term (κ : ℝ) (χ : EisensteinIdealExponent → ℂ)
    (ν : EisensteinIdealExponent) {t : ℝ} (ht : 0 < t) :
    χ ν*((idealExponentNorm ν*t/1)^κ*Real.exp (-idealExponentNorm ν*t/1):ℝ) =
      (t:ℂ)^(κ:ℂ) * (χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)*
        (Real.exp (-idealExponentNorm ν*t):ℝ)) := by
  have hn := idealExponentNorm_pos ν
  rw [div_one,div_one,Real.mul_rpow hn.le ht.le,Complex.ofReal_mul,
    Complex.ofReal_mul,Complex.ofReal_cpow hn.le,Complex.ofReal_cpow ht.le]
  ring

lemma idealHeatTheta_one_factor (κ : ℝ) (χ : EisensteinIdealExponent → ℂ)
    {t : ℝ} (ht : 0 < t) :
    idealHeatTheta 1 κ χ t = (t:ℂ)^(κ:ℂ)*
      idealTheta 1 (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)) t := by
  unfold idealHeatTheta idealTheta
  simp_rw [idealHeatTheta_one_term κ χ _ ht,div_one]
  exact tsum_mul_left

lemma idealHeatTheta_one_mellin {κ : ℝ} (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (idealHeatTheta 1 κ χ) s =
      Complex.Gamma (s+(κ:ℂ))*normDirichletSeries χ idealExponentNorm s := by
  have hsum : Summable (fun ν => ‖χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)‖ /
      idealExponentNorm ν^(s+(κ:ℂ)).re) := by
    convert summable_ideal_character_weight hs χ hχ using 1
    all_goals try with_reducible_and_instances rfl
    ext ν
    have hn := idealExponentNorm_pos ν
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hn,Complex.ofReal_re,
      Complex.add_re,Complex.ofReal_re,Real.rpow_add hn,Real.rpow_neg hn.le]
    field_simp
  have hseries (t : ℝ) (ht : 0 < t) :
      HasSum (fun ν => (χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ))*
        (Real.exp (-idealExponentNorm ν*t):ℝ))
        (idealTheta 1 (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)) t) := by
    have hh := idealHeatTheta_summable zero_lt_one hκ ht χ hχ
    simp_rw [idealHeatTheta_one_term κ χ _ ht] at hh
    have hc : (t:ℂ)^(κ:ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
    have hraw := (summable_mul_left_iff hc).mp hh
    simpa only [idealTheta,div_one] using hraw.hasSum
  have hm := hasSum_mellin (fun ν => Or.inr (idealExponentNorm_pos ν))
    (show 0 < (s+(κ:ℂ)).re by simp only [Complex.add_re,Complex.ofReal_re]; linarith)
    hseries hsum
  have he : mellin (idealHeatTheta 1 κ χ) s =
      mellin (idealTheta 1 (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ))) (s+(κ:ℂ)) := by
    rw [←mellin_cpow_smul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [idealHeatTheta_one_factor κ χ ht,smul_eq_mul]
  rw [he,←hm.tsum_eq]
  have ht (ν : EisensteinIdealExponent) :
      Complex.Gamma (s+(κ:ℂ))*(χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)) /
        (idealExponentNorm ν:ℂ)^(s+(κ:ℂ)) =
      Complex.Gamma (s+(κ:ℂ))*(χ ν*(idealExponentNorm ν:ℂ)^(-s)) := by
    have hn := Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'
    rw [Complex.cpow_add _ _ hn,Complex.cpow_neg]
    have hnk : (idealExponentNorm ν:ℂ)^(κ:ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
    field_simp
  simp_rw [ht]
  exact tsum_mul_left

lemma idealHeatTheta_scale (A κ : ℝ) (χ : EisensteinIdealExponent → ℂ) :
    idealHeatTheta A κ χ = fun t => idealHeatTheta 1 κ χ (t*(1/A)) := by
  funext t
  unfold idealHeatTheta
  apply tsum_congr
  intro ν
  have he : idealExponentNorm ν*t/A = idealExponentNorm ν*(t*(1/A))/1 := by ring
  have he' : -idealExponentNorm ν*t/A = -idealExponentNorm ν*(t*(1/A))/1 := by ring
  rw [he,he']

lemma idealHeatTheta_mellin {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (idealHeatTheta A κ χ) s =
      (A:ℂ)^s*Complex.Gamma (s+(κ:ℂ))*normDirichletSeries χ idealExponentNorm s := by
  rw [idealHeatTheta_scale A κ χ,mellin_comp_mul_right _ _ (one_div_pos.mpr hA),
    idealHeatTheta_one_mellin hκ χ hχ hs]
  have hp : ((1/A:ℝ):ℂ)^(-s) = (A:ℂ)^s := by
    simpa using mellin_scale_cpow zero_lt_one hA s
  rw [hp,smul_eq_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShiftedThetaCompletion
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decompletion with the fixed angular Gamma shift. The normalized heat
kernel has symmetry weight one, so the functional equation remains s ↦ 1-s. -/
noncomputable section
namespace CubicFirstMoment

lemma shiftedThetaHeckeL_differentiable {A κ : ℝ} (hA : 0 < A) {Λ : ℂ → ℂ}
    (hΛ : Differentiable ℂ Λ) : Differentiable ℂ (shiftedThetaHeckeL A κ Λ) := by
  let _ : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  exact (((differentiable_const_cpow_of_neZero (A:ℂ)).comp differentiable_neg).mul
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const (κ:ℂ)))).mul hΛ

lemma shiftedThetaHeckeL_completed {A κ : ℝ} (hA : 0 < A) (Λ : ℂ → ℂ) (s : ℂ)
    (hs : Complex.Gamma (s+(κ:ℂ)) ≠ 0) :
    heckeCompleted A κ (shiftedThetaHeckeL A κ Λ) s = Λ s := by
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  simp only [heckeCompleted,shiftedThetaHeckeL,Complex.cpow_neg]
  field_simp

lemma shiftedThetaHeckeL_functionalEquation {A κ : ℝ} (hA : 0 < A)
    (P : WeakFEPair ℂ) (hk : P.k = 1) :
    HeckeFunctionalEquation A κ P.ε
      (shiftedThetaHeckeL A κ P.Λ) (shiftedThetaHeckeL A κ P.symm.Λ) := by
  intro s hs hdual
  rw [shiftedThetaHeckeL_completed hA _ _ hs,shiftedThetaHeckeL_completed hA _ _ hdual]
  have he := P.functional_equation (1-s)
  simpa only [hk,Complex.ofReal_one,sub_sub_cancel,smul_eq_mul] using he

lemma shiftedThetaHeckeL_finiteOrder {A κ : ℝ} (hA : 0 < A)
    {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖Λ s‖ ≤ Real.exp (C*(1+‖s‖)^2)) :
    ShiftedCompletedHeckeFiniteOrder A κ (shiftedThetaHeckeL A κ Λ) :=
  ⟨Λ,hΛ,(fun s hs => (shiftedThetaHeckeL_completed hA Λ s hs).symm),C,hC,hbound⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaUpperMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative Mellin bounds on the exponentially decaying half of theta. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace CubicFirstMoment

lemma theta_mellin_exponent_bound {c t : ℝ} (hc : 0 < c) (ht : 1 ≤ t) (s : ℂ) :
    Real.log t * (s.re-1) - c*t ≤
      2*(1+‖s‖)^2/c - (c/2)*t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hl0 := Real.log_nonneg ht
  have hl : Real.log t ≤ 2*Real.sqrt t := by
    have hh := Real.log_le_rpow_div ht0.le (show 0 < (1/2:ℝ) by norm_num)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have hr : s.re-1 ≤ 1+‖s‖ := by linarith [Complex.re_le_norm s]
  have h1 := mul_le_mul_of_nonneg_left hr hl0
  have h2 := mul_le_mul_of_nonneg_right hl (show 0 ≤ 1+‖s‖ by positivity)
  have hsq := sq_nonneg (c*Real.sqrt t - 2*(1+‖s‖))
  have hroot := Real.sq_sqrt ht0.le
  have hdiv : c*(2*(1+‖s‖)^2/c) = 2*(1+‖s‖)^2 :=
    mul_div_cancel₀ _ hc.ne'
  have hsq' : 0 ≤ c^2*t-4*c*(1+‖s‖)*Real.sqrt t+4*(1+‖s‖)^2 := by
    calc
      0 ≤ (c*Real.sqrt t - 2*(1+‖s‖))^2 := hsq
      _ = c^2*(Real.sqrt t)^2-4*c*(1+‖s‖)*Real.sqrt t+4*(1+‖s‖)^2 := by ring
      _ = _ := by rw [hroot]
  have hy : 2*(1+‖s‖)*Real.sqrt t ≤ c*t/2 + 2*(1+‖s‖)^2/c := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith only [hsq',hdiv]
  nlinarith

lemma theta_mellin_integrand_bound {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t))
    (s : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t:ℂ)^(s-1)*f t‖ ≤
      (C*Real.exp (2*(1+‖s‖)^2/c))*Real.exp (-(c/2)*t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  calc
    _ ≤ t^((s-1).re)*(C*Real.exp (-c*t)) :=
      mul_le_mul_of_nonneg_left (hf t ht) (Real.rpow_nonneg ht0.le _)
    _ = C*Real.exp (Real.log t*(s.re-1)-c*t) := by
      rw [Real.rpow_def_of_pos ht0,Complex.sub_re,Complex.one_re,
        show Real.log t*(s.re-1)-c*t = Real.log t*(s.re-1)+(-c*t) by ring,Real.exp_add]
      ring
    _ ≤ C*Real.exp (2*(1+‖s‖)^2/c-(c/2)*t) := by
      have hC : 0 ≤ C := by
        have hh := (_root_.norm_nonneg (f 1)).trans (hf 1 le_rfl)
        exact nonneg_of_mul_nonneg_left hh (Real.exp_pos _)
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (theta_mellin_exponent_bound hc ht s)) hC
    _ = _ := by
      rw [show 2*(1+‖s‖)^2/c-(c/2)*t = 2*(1+‖s‖)^2/c+(-(c/2)*t) by ring, Real.exp_add]
      ring

lemma theta_upper_integrable {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hfcont : ContinuousOn f (Ioi 0))
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t)) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1)*f t) (Ioi 1) := by
  have hg := (integrableOn_exp_mul_Ioi (show -(c/2) < 0 by linarith) 1).const_mul
    (C*Real.exp (2*(1+‖s‖)^2/c))
  apply hg.mono' _
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
      theta_mellin_integrand_bound hc hf s ht.le))
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  apply ContinuousOn.mul _ (hfcont.mono (Ioi_subset_Ioi (by norm_num)))
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0)).continuousWithinAt

lemma theta_upper_norm_bound {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t)) (s : ℂ) :
    ‖∫ t : ℝ in Ioi 1, (t:ℂ)^(s-1)*f t‖ ≤
      (2*C/c)*Real.exp (2*(1+‖s‖)^2/c) := by
  have hC : 0 ≤ C := by
    have hh := (_root_.norm_nonneg (f 1)).trans (hf 1 le_rfl)
    exact nonneg_of_mul_nonneg_left hh (Real.exp_pos _)
  calc
    _ ≤ ∫ t : ℝ in Ioi 1,
        (C*Real.exp (2*(1+‖s‖)^2/c))*Real.exp (-(c/2)*t) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi (show -(c/2) < 0 by linarith) 1).const_mul _)
      exact ae_restrict_of_forall_mem measurableSet_Ioi
        (fun t ht => theta_mellin_integrand_bound hc hf s ht.le)
    _ = (C*Real.exp (2*(1+‖s‖)^2/c))*(2/c)*Real.exp (-(c/2)) := by
      rw [integral_const_mul,integral_exp_mul_Ioi (show -(c/2) < 0 by linarith)]
      field_simp
    _ ≤ (C*Real.exp (2*(1+‖s‖)^2/c))*(2/c)*1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaMellinSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed theta Mellin transform as two rapidly convergent tails. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

lemma mellin_thetaUpper (f : ℝ → ℂ) (s : ℂ) :
    mellin (thetaUpper f) s = ∫ t : ℝ in Ioi 1, (t:ℂ)^(s-1)*f t := by
  simp only [mellin,thetaUpper,← indicator_smul]
  rw [setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  rfl

lemma thetaUpper_mellinConvergent {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hfcont : ContinuousOn f (Ioi 0))
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t)) (s : ℂ) :
    MellinConvergent (thetaUpper f) s := by
  simp only [MellinConvergent,thetaUpper,← indicator_smul]
  rw [IntegrableOn,integrable_indicator_iff measurableSet_Ioi]
  change Integrable _ ((volume.restrict (Ioi 0)).restrict (Ioi 1))
  rw [Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  exact theta_upper_integrable hc hfcont hf s

lemma theta_mellin_split {f g : ℝ → ℂ} {ε : ℂ}
    (hFE : ∀ t : ℝ, 0 < t → f (1/t) = ε*(t:ℂ)*g t)
    {s : ℂ} (hf : MellinConvergent (thetaUpper f) s)
    (hg : MellinConvergent (thetaUpper g) (1-s)) :
    mellin f s = mellin (thetaUpper f) s + ε*mellin (thetaUpper g) (1-s) := by
  let v : ℝ → ℂ := fun t => ε • ((t:ℂ)^(-1:ℂ) • thetaUpper g t⁻¹)
  have hginv : MellinConvergent (fun t : ℝ => thetaUpper g t⁻¹) (s-1) := by
    have he : (s-1)/(-1:ℝ) = 1-s := by push_cast; ring
    rw [← he] at hg
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (by norm_num : (-1:ℝ) ≠ 0)).mpr hg
  have hv : MellinConvergent v s := by
    exact (MellinConvergent.cpow_smul.mpr (by simpa only [sub_eq_add_neg] using hginv)).const_smul ε
  have hid : f =ᵐ[volume.restrict (Ioi 0)] (fun t => thetaUpper f t + v t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (volume.restrict (Ioi 0)).ae_ne 1] with t ht ht1
    change 0 < t at ht
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hlt
      have ht' := hFE t⁻¹ (inv_pos.mpr ht)
      simp only [one_div,inv_inv,Complex.ofReal_inv] at ht'
      rw [thetaUpper,indicator_of_notMem (show t ∉ Ioi (1:ℝ) from not_lt.mpr hlt.le),zero_add]
      dsimp only [v]
      rw [thetaUpper,indicator_of_mem (show t⁻¹ ∈ Ioi (1:ℝ) from hinv),smul_eq_mul,smul_eq_mul,
        Complex.cpow_neg_one]
      simpa only [mul_assoc] using ht'
    · have hinv : t⁻¹ < 1 := (inv_lt_one₀ ht).mpr hgt
      rw [thetaUpper,indicator_of_mem (show t ∈ Ioi (1:ℝ) from hgt)]
      dsimp only [v]
      rw [thetaUpper,indicator_of_notMem (show t⁻¹ ∉ Ioi (1:ℝ) from not_lt.mpr hinv.le)]
      simp
  calc
    mellin f s = mellin (fun t => thetaUpper f t + v t) s := by
      apply integral_congr_ae
      filter_upwards [hid] with t ht
      rw [ht]
    _ = mellin (thetaUpper f) s + mellin v s := (hasMellin_add hf hv).2
    _ = _ := by
      dsimp only [v]
      rw [mellin_const_smul,mellin_cpow_smul,mellin_comp_inv]
      simp only [smul_eq_mul,show -(s+(-1:ℂ)) = 1-s by ring]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaMellinGrowth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic exponential growth bound derived from theta decay and inversion. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma theta_mellin_growth {f g : ℝ → ℂ} {ε : ℂ} {C D c : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfcont : ContinuousOn f (Ioi 0)) (hgcont : ContinuousOn g (Ioi 0))
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t))
    (hg : ∀ t : ℝ, 1 ≤ t → ‖g t‖ ≤ D*Real.exp (-c*t))
    (hFE : ∀ t : ℝ, 0 < t → f (1/t) = ε*(t:ℂ)*g t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖mellin f s‖ ≤ Real.exp (B*(1+‖s‖)^2) := by
  let K := 2*C/c+‖ε‖*(2*D/c)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+8/c,by positivity,?_⟩
  intro s
  have hf' := thetaUpper_mellinConvergent hc hfcont hf s
  have hg' := thetaUpper_mellinConvergent hc hgcont hg (1-s)
  have hsplit := theta_mellin_split hFE hf' hg'
  have hfb := theta_upper_norm_bound hc hf s
  have hgb := theta_upper_norm_bound hc hg (1-s)
  have hn : 1+‖1-s‖ ≤ 2*(1+‖s‖) := by
    have hh := norm_sub_le (1:ℂ) s
    rw [norm_one] at hh
    linarith [_root_.norm_nonneg s]
  have hnsq : (1+‖1-s‖)^2 ≤ 4*(1+‖s‖)^2 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ 1+‖1-s‖ by positivity) hn 2
    nlinarith
  have hexp : Real.exp (2*(1+‖1-s‖)^2/c) ≤ Real.exp ((8/c)*(1+‖s‖)^2) := by
    apply Real.exp_le_exp.mpr
    have hh : 2*(1+‖1-s‖)^2 ≤ 8*(1+‖s‖)^2 := by linarith
    convert div_le_div_of_nonneg_right hh hc.le using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hexp' : Real.exp (2*(1+‖s‖)^2/c) ≤ Real.exp ((8/c)*(1+‖s‖)^2) := by
    apply Real.exp_le_exp.mpr
    have hh : 2*(1+‖s‖)^2 ≤ 8*(1+‖s‖)^2 := by nlinarith [sq_nonneg (1+‖s‖)]
    convert div_le_div_of_nonneg_right hh hc.le using 1
    all_goals try with_reducible_and_instances rfl
    ring
  calc
    ‖mellin f s‖ ≤ ‖mellin (thetaUpper f) s‖+‖ε*mellin (thetaUpper g) (1-s)‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ = ‖mellin (thetaUpper f) s‖+‖ε‖*‖mellin (thetaUpper g) (1-s)‖ := by rw [norm_mul]
    _ ≤ (2*C/c)*Real.exp (2*(1+‖s‖)^2/c)+
        ‖ε‖*((2*D/c)*Real.exp (2*(1+‖1-s‖)^2/c)) := by
      rw [mellin_thetaUpper,mellin_thetaUpper]
      exact add_le_add hfb (mul_le_mul_of_nonneg_left hgb (_root_.norm_nonneg ε))
    _ ≤ K*Real.exp ((8/c)*(1+‖s‖)^2) := by
      calc
        _ ≤ (2*C/c)*Real.exp ((8/c)*(1+‖s‖)^2)+
            ‖ε‖*((2*D/c)*Real.exp ((8/c)*(1+‖s‖)^2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hexp' (by positivity))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity))
              (_root_.norm_nonneg ε))
        _ = _ := by dsimp [K]; ring
    _ ≤ Real.exp K*Real.exp ((8/c)*(1+‖s‖)^2) :=
      mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp K)) (Real.exp_pos _).le
    _ ≤ Real.exp ((K+8/c)*(1+‖s‖)^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hq : 1 ≤ (1+‖s‖)^2 := one_le_pow₀ (by linarith [_root_.norm_nonneg s])
      nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealHeatCompletion
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire angular Hecke completion from the actual normalized heat
transformation. No continuation or finite-order assumption is used here. -/
noncomputable section
open Filter Asymptotics MeasureTheory
namespace CubicFirstMoment

lemma shiftedThetaHeckeL_eq_series {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    shiftedThetaHeckeL A κ (mellin (idealHeatTheta A κ χ)) s =
      normDirichletSeries χ idealExponentNorm s := by
  rw [shiftedThetaHeckeL,idealHeatTheta_mellin hA hκ χ hχ hs,Complex.cpow_neg]
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (show 0 < (s+(κ:ℂ)).re by simp only [Complex.add_re,Complex.ofReal_re]; linarith)
  field_simp

lemma idealHeat_completion {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealHeatTheta A κ χ (1/t) = ε*(t:ℂ)*idealHeatTheta A κ χdual t) :
    ∃ L Ldual : ℂ → ℂ, Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s) ∧
      HeckeFunctionalEquation A κ ε L Ldual ∧ ShiftedCompletedHeckeFiniteOrder A κ L := by
  let P := idealHeatFEPair hA hκ χ χdual hχ hχdual hε hFE
  have hP : IsStrongFEPair P := ⟨rfl,rfl⟩
  refine ⟨shiftedThetaHeckeL A κ P.Λ,shiftedThetaHeckeL A κ P.symm.Λ,
    shiftedThetaHeckeL_differentiable hA hP.differentiable_Λ,?_,?_,
    shiftedThetaHeckeL_functionalEquation hA P rfl,?_⟩
  · intro s hs
    rw [hP.Λ_eq]
    exact shiftedThetaHeckeL_eq_series hA hκ χ hχ hs
  · intro s hs
    rw [hP.symm_Λ_eq]
    exact shiftedThetaHeckeL_eq_series hA hκ χdual hχdual hs
  · obtain ⟨C,hC,hfb⟩ := idealHeatTheta_norm_bound hA hκ χ hχ
    obtain ⟨D,hD,hgb⟩ := idealHeatTheta_norm_bound hA hκ χdual hχdual
    have hf (t : ℝ) (ht : 1 ≤ t) :
        ‖idealHeatTheta A κ χ t‖ ≤ C*Real.exp (-(1/(4*A))*t) := by
      convert hfb t ht using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      ring
    have hg (t : ℝ) (ht : 1 ≤ t) :
        ‖idealHeatTheta A κ χdual t‖ ≤ D*Real.exp (-(1/(4*A))*t) := by
      convert hgb t ht using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      ring
    obtain ⟨B,hB,hbound⟩ := theta_mellin_growth (show 0 < 1/(4*A) by positivity)
      hC hD (idealHeatTheta_continuousOn hA hκ χ hχ)
      (idealHeatTheta_continuousOn hA hκ χdual hχdual) hf hg hFE
    apply shiftedThetaHeckeL_finiteOrder hA hP.differentiable_Λ hB
    intro s
    rw [hP.Λ_eq]
    exact hbound s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeatLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact angular ideal/element theta reindexing, including all finite
Euler factors and the term at zero. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma angular_char_unit_mul (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (x : EisensteinIdealExponent × Eisensteinˣ) :
    χ (Ideal.Quotient.mk (modulus q) (idealElementCoordinates x).val)*
      theta ℓ (idealElementCoordinates x).val = angularResidueIdealChar q χ ℓ x.1 := by
  change χ (Ideal.Quotient.mk (modulus q) ((x.2:Eisenstein)*idealExponentGenerator x.1))*
    theta ℓ ((x.2:Eisenstein)*idealExponentGenerator x.1) = _
  rw [map_mul,map_mul,theta_mul]
  calc
    _ = (χ (Ideal.Quotient.mk (modulus q) x.2)*theta ℓ x.2)*
      (χ (Ideal.Quotient.mk (modulus q) (idealExponentGenerator x.1))*
        theta ℓ (idealExponentGenerator x.1)) := by ring
    _ = _ := by rw [hu,one_mul]; rfl

lemma angular_unitCompatible_dual {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ) :
    AngularUnitCompatible q (star χ) (-ℓ) := by
  intro u
  rw [MulChar.star_apply,←star_theta u.ne_zero ℓ,←star_mul,mul_comm (theta ℓ u),hu u,star_one]

lemma idealHeatTheta_lattice {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    {A κ t : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) (ht : 0 < t) :
    (∑' a : {a : Eisenstein // a ≠ 0},
      (χ (Ideal.Quotient.mk (modulus q) a.val)*theta ℓ a.val)*
        ((norm a.val*t/A)^κ*Real.exp (-norm a.val*t/A):ℝ)) =
      (Nat.card (Eisensteinˣ):ℂ)*idealHeatTheta A κ (angularResidueIdealChar q χ ℓ) t := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  let f : EisensteinIdealExponent → ℂ := fun ν =>
    angularResidueIdealChar q χ ℓ ν*
      ((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)
  have hf : Summable f := idealHeatTheta_summable hA hκ ht _
    (angularResidueIdealChar_norm_le_one hq χ ℓ)
  have hprod : Summable (fun x : EisensteinIdealExponent × Eisensteinˣ => f x.1) := by
    simpa only [mul_one] using summable_mul_of_summable_norm
      (g := fun _ : Eisensteinˣ => (1:ℂ)) hf.norm (hasSum_fintype _).summable
  rw [←idealElementCoordinates.tsum_eq]
  have he : (fun x : EisensteinIdealExponent × Eisensteinˣ =>
      (χ (Ideal.Quotient.mk (modulus q) (idealElementCoordinates x).val)*
        theta ℓ (idealElementCoordinates x).val)*
      ((norm (idealElementCoordinates x).val*t/A)^κ*
        Real.exp (-norm (idealElementCoordinates x).val*t/A):ℝ)) = fun x => f x.1 := by
    funext x
    rw [angular_char_unit_mul q χ ℓ hu,idealElementCoordinates_norm]
  rw [he,hprod.tsum_prod' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [tsum_mul_left]
  simp only [Nat.card_eq_fintype_card]
  rfl

lemma theta_at_zero {ℓ : ℤ} (hℓ : ℓ ≠ 0) : theta ℓ (0:Eisenstein) = 0 := by
  simp only [theta,Subalgebra.coe_zero,norm_zero,Complex.ofReal_zero,div_zero]
  exact zero_zpow _ hℓ

lemma angularLatticeHeat_eq {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (hn : ℓ ≠ 0 ∨ χ ≠ 1)
    {A κ t : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) (ht : 0 < t) :
    angularLatticeHeat q χ ℓ A κ t =
      (Nat.card (Eisensteinˣ):ℂ)*idealHeatTheta A κ (angularResidueIdealChar q χ ℓ) t := by
  rw [←idealHeatTheta_lattice hq χ ℓ hu hA hκ ht]
  symm
  unfold angularLatticeHeat
  apply tsum_subtype_eq_of_support_subset (s := {a : Eisenstein | a ≠ 0})
    (f := fun a : Eisenstein => (χ (Ideal.Quotient.mk (modulus q) a)*theta ℓ a)*
      ((norm a*t/A)^κ*Real.exp (-norm a*t/A):ℝ))
  intro a ha
  by_contra he
  have hz : a = 0 := not_not.mp he
  subst a
  rcases hn with hℓ | hχ
  · simp only [Function.mem_support,theta_at_zero hℓ,mul_zero,zero_mul,ne_eq,not_true_eq_false] at ha
  · let : Nontrivial (Residues q) := residue_nontrivial_of_nonprincipal χ hχ
    simp only [Function.mem_support,map_zero,MulChar.map_zero,zero_mul,ne_eq,not_true_eq_false] at ha

lemma angularHeat_inversion_of_lattice {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (hn : ℓ ≠ 0 ∨ χ ≠ 1) {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) {root : ℂ}
    (hFE : ∀ t : ℝ, 0 < t → angularLatticeHeat q χ ℓ A κ (1/t) =
      root*(t:ℂ)*angularLatticeHeat q (star χ) (-ℓ) A κ t) :
    ∀ t : ℝ, 0 < t → idealHeatTheta A κ (angularResidueIdealChar q χ ℓ) (1/t) =
      root*(t:ℂ)*idealHeatTheta A κ (angularResidueIdealChar q (star χ) (-ℓ)) t := by
  have hd := angular_unitCompatible_dual hu
  have hnd : -ℓ ≠ 0 ∨ star χ ≠ 1 := by
    rcases hn with hℓ | hχ
    · exact Or.inl (neg_ne_zero.mpr hℓ)
    · right
      intro h
      apply hχ
      simpa using congrArg star h
  intro t ht
  have h := hFE t ht
  rw [angularLatticeHeat_eq hq χ ℓ hu hn hA hκ (one_div_pos.mpr ht),
    angularLatticeHeat_eq hq (star χ) (-ℓ) hd hnd hA hκ ht] at h
  apply mul_left_cancel₀ residueTheta_unit_multiplicity_ne_zero
  calc
    _ = root*(t:ℂ)*((Nat.card (Eisensteinˣ):ℂ)*
      idealHeatTheta A κ (angularResidueIdealChar q (star χ) (-ℓ)) t) := h
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeatPolynomial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular phase times its radial weight is a harmonic monomial. -/
noncomputable section
namespace CubicFirstMoment

lemma norm_half_nat_rpow (a : Eisenstein) (n : ℕ) :
    (norm a)^((n:ℝ)/2) = ‖(a:ℂ)‖^n := by
  rw [eisenstein_norm_eq_sq,←Real.rpow_natCast ‖a‖ 2,←Real.rpow_mul (_root_.norm_nonneg a)]
  have he : (2:ℝ)*((n:ℝ)/2) = n := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he,Real.rpow_natCast]
  rfl

lemma theta_nat_radial {a : Eisenstein} (ha : a ≠ 0) (n : ℕ) :
    theta (n:ℤ) a*((norm a)^((n:ℝ)/2):ℝ) = (a:ℂ)^n := by
  have haC : (a:ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  have hn : (‖(a:ℂ)‖:ℂ)^n ≠ 0 := pow_ne_zero _
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr haC))
  rw [norm_half_nat_rpow,Complex.ofReal_pow]
  simp only [theta,zpow_natCast,div_pow]
  exact div_mul_cancel₀ _ hn

lemma theta_neg_nat_radial {a : Eisenstein} (ha : a ≠ 0) (n : ℕ) :
    theta (-(n:ℤ)) a*((norm a)^((n:ℝ)/2):ℝ) = (star (a:ℂ))^n := by
  rw [←star_theta ha]
  simpa only [star_mul,Complex.star_def,Complex.conj_ofReal,map_pow,mul_comm] using
    congrArg star (theta_nat_radial ha n)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HarmonicGaussian
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic polynomial Gaussians and the anti-holomorphic raising
operator used for the fixed angular Fourier transform. -/
noncomputable section
open scoped SchwartzMap
open LineDeriv
namespace CubicFirstMoment

lemma gaussianComplex_fderiv (a : ℝ) (ha : 0 < a) (z v : ℂ) :
    fderiv ℝ (radialGaussianSchwartz a ha) z v =
      ((-2*a*inner ℝ z v*radialGaussian a z:ℝ):ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((radialGaussian_smooth a).differentiable (by simp) |>.differentiableAt.hasFDerivAt)
  have he : (radialGaussianSchwartz a ha : ℂ → ℂ) = Complex.ofRealCLM ∘ radialGaussian a := rfl
  rw [he,h.fderiv,radialGaussian_fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    gaussianLogDerivative,smul_eq_mul,Complex.ofRealCLM_apply]
  congr 1
  change radialGaussian a z*((-2*a)*inner ℝ z v) = -2*a*inner ℝ z v*radialGaussian a z
  ring

lemma harmonicGaussian_fderiv (a : ℝ) (ha : 0 < a) (n : ℕ) (z v : ℂ) :
    fderiv ℝ (harmonicGaussian a ha n) z v =
      (n:ℂ)*z^(n-1)*v*(radialGaussian a z:ℂ) +
        z^n*((-2*a*inner ℝ z v*radialGaussian a z:ℝ):ℂ) := by
  have he : (harmonicGaussian a ha n : ℂ → ℂ) =
      (fun z : ℂ => z^n*radialGaussianSchwartz a ha z) := by
    ext z
    exact harmonicGaussian_apply a ha n z
  rw [he,fderiv_fun_mul (by fun_prop) (radialGaussianSchwartz a ha).differentiableAt]
  simp only [add_apply,smul_apply,
    smul_eq_mul, fderiv_pow_ring,ContinuousLinearMap.id_apply,nsmul_eq_mul,
    gaussianComplex_fderiv,radialGaussianSchwartz_apply,radialGaussian]
  ring

lemma harmonicGaussian_raising (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∂_{(1:ℂ)} (harmonicGaussian a ha n)) +
      Complex.I • (∂_{Complex.I} (harmonicGaussian a ha n)) =
        ((-2*a:ℝ):ℂ) • harmonicGaussian a ha (n+1) := by
  ext z
  simp only [add_apply,smul_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,harmonicGaussian_fderiv,
    harmonicGaussian_apply,smul_eq_mul]
  have hi1 : inner ℝ z (1:ℂ) = z.re := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  have hiI : inner ℝ z Complex.I = z.im := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  rw [hi1,hiI,pow_succ]
  push_cast
  have hz : (z.re:ℂ)+(z.im:ℂ)*Complex.I = z := Complex.re_add_im z
  calc
    _ = (-2*(a:ℂ))*z^n*((z.re:ℂ)+(z.im:ℂ)*Complex.I)*(radialGaussian a z:ℂ) := by
      ring_nf
      simp only [Complex.I_sq]
      ring
    _ = _ := by rw [hz]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HarmonicGaussianFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Fourier transform of every holomorphic polynomial Gaussian. -/
noncomputable section
open scoped SchwartzMap FourierTransform
open LineDeriv FourierTransform
namespace CubicFirstMoment

lemma harmonicGaussian_fourier_step (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) :
    𝓕 (harmonicGaussian a ha (n+1)) w =
      (-(Real.pi:ℂ)*Complex.I/(a:ℂ))*w*𝓕 (harmonicGaussian a ha n) w := by
  have ht (m : ℂ) : (fun x : ℂ => inner ℝ x m).HasTemperateGrowth := by fun_prop
  have h := congrArg (fun f : 𝓢(ℂ,ℂ) => 𝓕 f w) (harmonicGaussian_raising a ha n)
  simp only [FourierTransform.fourier_add,FourierTransform.fourier_smul,SchwartzMap.fourier_lineDerivOp_eq,
    add_apply,smul_apply,SchwartzMap.smulLeftCLM_apply_apply
      (ht 1),
    SchwartzMap.smulLeftCLM_apply_apply
      (ht Complex.I),smul_eq_mul] at h
  have hi1 : inner ℝ w (1:ℂ) = w.re := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  have hiI : inner ℝ w Complex.I = w.im := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  rw [hi1,hiI] at h
  simp only [Complex.real_smul] at h
  have hw : (w.re:ℂ)+(w.im:ℂ)*Complex.I = w := Complex.re_add_im w
  have he : (2*(Real.pi:ℂ)*Complex.I)*w*𝓕 (harmonicGaussian a ha n) w =
      ((-2*a:ℝ):ℂ)*𝓕 (harmonicGaussian a ha (n+1)) w := by
    calc
      _ = (2*(Real.pi:ℂ)*Complex.I)*((w.re:ℂ)+(w.im:ℂ)*Complex.I)*
          𝓕 (harmonicGaussian a ha n) w := by rw [hw]
      _ = _ := by convert h using 1; ring
  have haC : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  apply (mul_left_cancel₀ (show (-2:ℂ)*(a:ℂ) ≠ 0 by exact mul_ne_zero (by norm_num) haC))
  push_cast at he
  calc
    _ = (2*(Real.pi:ℂ)*Complex.I)*w*𝓕 (harmonicGaussian a ha n) w := he.symm
    _ = _ := by field_simp

lemma harmonicGaussian_fourier (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) :
    𝓕 (harmonicGaussian a ha n) w =
      (-(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*w^n*
        𝓕 (radialGaussianSchwartz a ha) w := by
  induction n with
  | zero =>
      have he : harmonicGaussian a ha 0 = radialGaussianSchwartz a ha := by
        ext z
        rw [harmonicGaussian_apply,pow_zero,one_mul]
        rfl
      simp only [he,pow_zero,one_mul]
  | succ n ih =>
      rw [harmonicGaussian_fourier_step,ih,pow_succ,pow_succ]
      ring

lemma harmonicGaussian_traceFourier (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) :
    traceFourier (harmonicGaussian a ha n) w =
      (-2*(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*(star w)^n*
        (Real.pi/a:ℝ)*(Real.exp (-4*Real.pi^2/a*Complex.normSq w):ℝ) := by
  rw [traceFourier_eq_fourier,←SchwartzMap.fourier_coe,harmonicGaussian_fourier]
  have hg := radialGaussianSchwartz_traceFourier a ha w
  rw [traceFourier_eq_fourier,←SchwartzMap.fourier_coe] at hg
  rw [hg,mul_pow]
  have he : (-(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*(2:ℂ)^n =
      (-2*(Real.pi:ℂ)*Complex.I/(a:ℂ))^n := by
    rw [←mul_pow]
    congr 1
    ring
  calc
    _ = ((-(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*(2:ℂ)^n)*(star w)^n*
      ((Real.pi/a:ℝ)*(Real.exp (-4*Real.pi^2/a*Complex.normSq w):ℝ)) := by ring
    _ = _ := by rw [he]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AntiHarmonicGaussian
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugate harmonic monomials, obtained by the measure-preserving
complex reflection. -/
noncomputable section
open scoped SchwartzMap FourierTransform
namespace CubicFirstMoment

lemma antiHarmonicGaussian_traceFourier (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) :
    traceFourier (antiHarmonicGaussian a ha n) w =
      (-2*(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*w^n*
        (Real.pi/a:ℝ)*(Real.exp (-4*Real.pi^2/a*Complex.normSq w):ℝ) := by
  have he : (antiHarmonicGaussian a ha n : ℂ → ℂ) =
      (harmonicGaussian a ha n) ∘ Complex.conjLIE := rfl
  rw [traceFourier_eq_fourier,he,Real.fourier_comp_linearIsometry]
  have h := harmonicGaussian_traceFourier a ha n (star w)
  rw [traceFourier_eq_fourier] at h
  simpa only [Complex.conjLIE_apply,map_mul,map_ofNat,star_star,Complex.star_def,Complex.conj_conj,
    Complex.normSq_conj] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueHarmonicPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic Poisson for the actual positive and negative angular
polynomial Gaussians. The finite Fourier coefficient is retained exactly. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma residueHarmonic_poisson {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    residueHarmonicTheta q χ A n t = (2/(Real.sqrt 3*norm q):ℝ) •
      ∑' h : Eisenstein, residueFiniteFourier q χ h *
        ((-2*(Real.pi:ℂ)*Complex.I/(t/A:ℝ))^n*
          (star ((h:ℂ)/((q:ℂ)*traceLambda)))^n*(Real.pi/(t/A):ℝ)*
          (Real.exp (-4*Real.pi^2/(t/A)*Complex.normSq ((h:ℂ)/((q:ℂ)*traceLambda))):ℝ)) := by
  have hp := poisson_eisenstein_periodic q hq (fun v => χ v)
    (harmonicGaussian (t/A) (div_pos ht hA) n)
  have he : (fun z : Eisenstein => χ (Ideal.Quotient.mk (modulus q) z)*
      harmonicGaussian (t/A) (div_pos ht hA) n (z:ℂ)) =
      fun z => χ (Ideal.Quotient.mk (modulus q) z)*
        ((z:ℂ)^n*(Real.exp (-norm z*t/A):ℝ)) := by
    funext z
    rw [harmonicGaussian_apply]
    unfold radialGaussian
    rw [eisenstein_norm_eq_sq]
    have hx : -(t/A)*‖(z:ℂ)‖^2 = -‖(z:ℂ)‖^2*t/A := by ring
    rw [hx]
    rfl
  rw [he] at hp
  simpa only [residueHarmonicTheta,residueFiniteFourier,harmonicGaussian_traceFourier] using hp

lemma residueAntiHarmonic_poisson {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    residueAntiHarmonicTheta q χ A n t = (2/(Real.sqrt 3*norm q):ℝ) •
      ∑' h : Eisenstein, residueFiniteFourier q χ h *
        ((-2*(Real.pi:ℂ)*Complex.I/(t/A:ℝ))^n*
          ((h:ℂ)/((q:ℂ)*traceLambda))^n*(Real.pi/(t/A):ℝ)*
          (Real.exp (-4*Real.pi^2/(t/A)*Complex.normSq ((h:ℂ)/((q:ℂ)*traceLambda))):ℝ)) := by
  have hp := poisson_eisenstein_periodic q hq (fun v => χ v)
    (antiHarmonicGaussian (t/A) (div_pos ht hA) n)
  have he : (fun z : Eisenstein => χ (Ideal.Quotient.mk (modulus q) z)*
      antiHarmonicGaussian (t/A) (div_pos ht hA) n (z:ℂ)) =
      fun z => χ (Ideal.Quotient.mk (modulus q) z)*
        ((star (z:ℂ))^n*(Real.exp (-norm z*t/A):ℝ)) := by
    funext z
    rw [antiHarmonicGaussian_apply]
    unfold radialGaussian
    rw [eisenstein_norm_eq_sq]
    have hx : -(t/A)*‖(z:ℂ)‖^2 = -‖(z:ℂ)‖^2*t/A := by ring
    rw [hx]
    rfl
  rw [he] at hp
  simpa only [residueAntiHarmonicTheta,residueFiniteFourier,antiHarmonicGaussian_traceFourier] using hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeatFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the normalized angular heat sum with the
polynomial Gaussian sum to which periodic Poisson applies. -/
noncomputable section
namespace CubicFirstMoment

lemma theta_nat_radial_all (a : Eisenstein) (n : ℕ) :
    theta (n:ℤ) a*((norm a)^((n:ℝ)/2):ℝ) = (a:ℂ)^n := by
  by_cases ha : a = 0
  · subst a
    cases n with
    | zero => simp [theta]
    | succ n =>
      simp only [theta,Subalgebra.coe_zero,norm_zero,Complex.ofReal_zero,div_zero,zpow_natCast]
      rw [zero_pow (Nat.succ_ne_zero n),zero_mul]
  · exact theta_nat_radial ha n

lemma theta_neg_nat_radial_all (a : Eisenstein) (n : ℕ) :
    theta (-(n:ℤ)) a*((norm a)^((n:ℝ)/2):ℝ) = (star (a:ℂ))^n := by
  by_cases ha : a = 0
  · subst a
    cases n with
    | zero => simp [theta]
    | succ n =>
      rw [theta_at_zero (by omega),zero_mul]
      simp
  · exact theta_neg_nat_radial ha n

lemma angularHeat_nat_factor (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    angularLatticeHeat q χ (n:ℤ) A ((n:ℝ)/2) t =
      ((t/A)^((n:ℝ)/2):ℝ)*residueHarmonicTheta q χ A n t := by
  unfold angularLatticeHeat residueHarmonicTheta
  rw [←tsum_mul_left]
  apply tsum_congr
  intro z
  have he : norm z*t/A = norm z*(t/A) := by ring
  rw [he,Real.mul_rpow (norm_nonneg z) (div_pos ht hA).le,Complex.ofReal_mul,
    Complex.ofReal_mul]
  calc
    _ = ((t/A)^((n:ℝ)/2):ℝ)*χ (Ideal.Quotient.mk (modulus q) z)*
        (theta (n:ℤ) z*((norm z)^((n:ℝ)/2):ℝ))*
        (Real.exp (-norm z*t/A):ℝ) := by ring
    _ = _ := by rw [theta_nat_radial_all]; ring

lemma angularHeat_neg_nat_factor (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    angularLatticeHeat q χ (-(n:ℤ)) A ((n:ℝ)/2) t =
      ((t/A)^((n:ℝ)/2):ℝ)*residueAntiHarmonicTheta q χ A n t := by
  unfold angularLatticeHeat residueAntiHarmonicTheta
  rw [←tsum_mul_left]
  apply tsum_congr
  intro z
  have he : norm z*t/A = norm z*(t/A) := by ring
  rw [he,Real.mul_rpow (norm_nonneg z) (div_pos ht hA).le,Complex.ofReal_mul,
    Complex.ofReal_mul]
  calc
    _ = ((t/A)^((n:ℝ)/2):ℝ)*χ (Ideal.Quotient.mk (modulus q) z)*
        (theta (-(n:ℤ)) z*((norm z)^((n:ℝ)/2):ℝ))*
        (Real.exp (-norm z*t/A):ℝ) := by ring
    _ = _ := by rw [theta_neg_nat_radial_all]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueHarmonicTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial Gaussian theta transformation before the final
normalization by the angular radial weight. -/
noncomputable section
namespace CubicFirstMoment

lemma residueHarmonic_transform {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h))
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    residueHarmonicTheta q χ (residueHeckeScale q) n t =
      (1/(Real.sqrt (norm q)*t):ℝ)*G*(angularConductorPhase q/(t:ℂ))^n*
        residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t) := by
  have hA := residueHeckeScale_pos hq
  rw [residueHarmonic_poisson hq χ hA ht]
  simp_rw [residueGaussian_exponent hq ht,hFourier]
  have hf (h : Eisenstein) :
      (G*(star χ) (Ideal.Quotient.mk (modulus q) h))*
        ((-2*(Real.pi:ℂ)*Complex.I/(t/residueHeckeScale q:ℝ))^n*
          (star ((h:ℂ)/((q:ℂ)*traceLambda)))^n*(Real.pi/(t/residueHeckeScale q):ℝ)*
          (Real.exp (-norm h/(residueHeckeScale q*t)):ℝ)) =
      (Real.pi/(t/residueHeckeScale q):ℝ)*G*(angularConductorPhase q/(t:ℂ))^n*
        ((star χ) (Ideal.Quotient.mk (modulus q) h)*
          ((star (h:ℂ))^n*(Real.exp (-norm h*(1/t)/residueHeckeScale q):ℝ))) := by
    have hexp : -norm h/(residueHeckeScale q*t) = -norm h*(1/t)/residueHeckeScale q := by ring
    rw [hexp,star_div₀]
    have hpoly : (-2*(Real.pi:ℂ)*Complex.I/(t/residueHeckeScale q:ℝ))*
        (star (h:ℂ)/star ((q:ℂ)*traceLambda)) =
      (angularConductorPhase q/(t:ℂ))*star (h:ℂ) := by
      unfold angularConductorPhase
      push_cast
      field_simp
    rw [←mul_pow,hpoly,mul_pow]
    ring
  simp_rw [hf]
  rw [tsum_mul_left]
  change ((2/(Real.sqrt 3*norm q):ℝ):ℂ)*
    (((Real.pi/(t/residueHeckeScale q):ℝ):ℂ)*G*(angularConductorPhase q/(t:ℂ))^n*
      residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t)) = _
  rw [show ((2/(Real.sqrt 3*norm q):ℝ):ℂ)*
      (((Real.pi/(t/residueHeckeScale q):ℝ):ℂ)*G*(angularConductorPhase q/(t:ℂ))^n*
        residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t)) =
      (((2/(Real.sqrt 3*norm q))*(Real.pi/(t/residueHeckeScale q)):ℝ):ℂ)*G*
        (angularConductorPhase q/(t:ℂ))^n*
          residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t) by push_cast; ring]
  rw [residueGaussian_prefactor hq ht]

lemma residueAntiHarmonic_transform {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h))
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    residueAntiHarmonicTheta q χ (residueHeckeScale q) n t =
      (1/(Real.sqrt (norm q)*t):ℝ)*G*(angularConductorPhaseNeg q/(t:ℂ))^n*
        residueHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t) := by
  have hA := residueHeckeScale_pos hq
  rw [residueAntiHarmonic_poisson hq χ hA ht]
  simp_rw [residueGaussian_exponent hq ht,hFourier]
  have hf (h : Eisenstein) :
      (G*(star χ) (Ideal.Quotient.mk (modulus q) h))*
        ((-2*(Real.pi:ℂ)*Complex.I/(t/residueHeckeScale q:ℝ))^n*
          ((h:ℂ)/((q:ℂ)*traceLambda))^n*(Real.pi/(t/residueHeckeScale q):ℝ)*
          (Real.exp (-norm h/(residueHeckeScale q*t)):ℝ)) =
      (Real.pi/(t/residueHeckeScale q):ℝ)*G*(angularConductorPhaseNeg q/(t:ℂ))^n*
        ((star χ) (Ideal.Quotient.mk (modulus q) h)*
          ((h:ℂ)^n*(Real.exp (-norm h*(1/t)/residueHeckeScale q):ℝ))) := by
    have hexp : -norm h/(residueHeckeScale q*t) = -norm h*(1/t)/residueHeckeScale q := by ring
    rw [hexp]
    have hpoly : (-2*(Real.pi:ℂ)*Complex.I/(t/residueHeckeScale q:ℝ))*
        ((h:ℂ)/((q:ℂ)*traceLambda)) =
      (angularConductorPhaseNeg q/(t:ℂ))*(h:ℂ) := by
      unfold angularConductorPhaseNeg
      push_cast
      field_simp
    rw [←mul_pow,hpoly,mul_pow]
    ring
  simp_rw [hf]
  rw [tsum_mul_left]
  change ((2/(Real.sqrt 3*norm q):ℝ):ℂ)*
    (((Real.pi/(t/residueHeckeScale q):ℝ):ℂ)*G*(angularConductorPhaseNeg q/(t:ℂ))^n*
      residueHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t)) = _
  rw [show ((2/(Real.sqrt 3*norm q):ℝ):ℂ)*
      (((Real.pi/(t/residueHeckeScale q):ℝ):ℂ)*G*(angularConductorPhaseNeg q/(t:ℂ))^n*
        residueHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t)) =
      (((2/(Real.sqrt 3*norm q))*(Real.pi/(t/residueHeckeScale q)):ℝ):ℂ)*G*
        (angularConductorPhaseNeg q/(t:ℂ))^n*
          residueHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t) by push_cast; ring]
  rw [residueGaussian_prefactor hq ht]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeatNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalization of the angular polynomial theta transformation. -/
noncomputable section
namespace CubicFirstMoment

lemma heat_radial_normalization {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    (1/t/A)^((n:ℝ)/2)*t^n = (t/A)^((n:ℝ)/2) := by
  have hp : t^n = (t^2)^((n:ℝ)/2) := by
    rw [←Real.rpow_natCast t 2,←Real.rpow_mul ht.le]
    have he : (2:ℝ)*((n:ℝ)/2) = n := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he,Real.rpow_natCast]
  rw [hp,←Real.mul_rpow (by positivity : 0 ≤ 1/t/A) (sq_nonneg t)]
  congr 1
  field_simp

lemma angularHeat_nat_transformation {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h))
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    angularLatticeHeat q χ (n:ℤ) (residueHeckeScale q) ((n:ℝ)/2) (1/t) =
      ((G/(Real.sqrt (norm q):ℝ))*(angularConductorPhase q)^n)*(t:ℂ)*
        angularLatticeHeat q (star χ) (-(n:ℤ)) (residueHeckeScale q) ((n:ℝ)/2) t := by
  have hA := residueHeckeScale_pos hq
  rw [angularHeat_nat_factor q χ hA (one_div_pos.mpr ht),
    residueHarmonic_transform hq χ G hFourier (one_div_pos.mpr ht),
    angularHeat_neg_nat_factor q (star χ) hA ht,one_div_one_div]
  have hp : (angularConductorPhase q/((1/t:ℝ):ℂ))^n =
      (angularConductorPhase q)^n*(t:ℂ)^n := by
    rw [Complex.ofReal_div,Complex.ofReal_one,div_div_eq_mul_div,div_one,mul_pow]
  rw [hp]
  have hr : (((1/t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ)*(t:ℂ)^n =
      (((t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ) := by
    exact_mod_cast heat_radial_normalization hA ht n
  have htC := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  calc
    _ = (G/(Real.sqrt (norm q):ℝ))*(angularConductorPhase q)^n*(t:ℂ)*
        ((((1/t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ)*(t:ℂ)^n)*
        residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n t := by
      field_simp
    _ = _ := by rw [hr]; ring

lemma angularHeat_neg_nat_transformation {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h))
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    angularLatticeHeat q χ (-(n:ℤ)) (residueHeckeScale q) ((n:ℝ)/2) (1/t) =
      ((G/(Real.sqrt (norm q):ℝ))*(angularConductorPhaseNeg q)^n)*(t:ℂ)*
        angularLatticeHeat q (star χ) (n:ℤ) (residueHeckeScale q) ((n:ℝ)/2) t := by
  have hA := residueHeckeScale_pos hq
  rw [angularHeat_neg_nat_factor q χ hA (one_div_pos.mpr ht),
    residueAntiHarmonic_transform hq χ G hFourier (one_div_pos.mpr ht),
    angularHeat_nat_factor q (star χ) hA ht,one_div_one_div]
  have hp : (angularConductorPhaseNeg q/((1/t:ℝ):ℂ))^n =
      (angularConductorPhaseNeg q)^n*(t:ℂ)^n := by
    rw [Complex.ofReal_div,Complex.ofReal_one,div_div_eq_mul_div,div_one,mul_pow]
  rw [hp]
  have hr : (((1/t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ)*(t:ℂ)^n =
      (((t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ) := by
    exact_mod_cast heat_radial_normalization hA ht n
  have htC := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  calc
    _ = (G/(Real.sqrt (norm q):ℝ))*(angularConductorPhaseNeg q)^n*(t:ℂ)*
        ((((1/t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ)*(t:ℂ)^n)*
        residueHarmonicTheta q (star χ) (residueHeckeScale q) n t := by
      field_simp
    _ = _ := by rw [hr]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeFromHeat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular Hecke analytic package follows from its finite
character theta transformation. This introduces no analytic input. -/
noncomputable section
namespace CubicFirstMoment

lemma angularHecke_from_heatTransformation {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (hn : ℓ ≠ 0 ∨ χ ≠ 1) (root : ℂ) (hr : ‖root‖ = 1)
    (hFE : ∀ t : ℝ, 0 < t →
      angularLatticeHeat q χ ℓ (residueHeckeScale q) (|(ℓ:ℝ)|/2) (1/t) =
        root*(t:ℂ)*angularLatticeHeat q (star χ) (-ℓ)
          (residueHeckeScale q) (|(ℓ:ℝ)|/2) t) :
    ∃ (L Ldual : ℂ → ℂ), Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s =
        normDirichletSeries (angularResidueIdealChar q χ ℓ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s =
        normDirichletSeries (angularResidueIdealChar q (star χ) (-ℓ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) (|(ℓ:ℝ)|/2) root L Ldual ∧
      ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) (|(ℓ:ℝ)|/2) L := by
  have hr0 : root ≠ 0 := by
    intro he
    rw [he,norm_zero] at hr
    norm_num at hr
  exact idealHeat_completion (residueHeckeScale_pos hq) (by positivity) _ _
    (angularResidueIdealChar_norm_le_one hq χ ℓ)
    (angularResidueIdealChar_norm_le_one hq (star χ) (-ℓ)) hr0
    (angularHeat_inversion_of_lattice hq χ ℓ hu hn (residueHeckeScale_pos hq) (by positivity) hFE)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeFromFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete angular analytic package constructed from the finite
Gauss Fourier identity and its norm, via the proved harmonic Poisson formula. -/
noncomputable section
namespace CubicFirstMoment

lemma angularHecke_from_finiteFourier {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (hn : ℓ ≠ 0 ∨ χ ≠ 1) (G : ℂ) (hG : ‖G‖ = Real.sqrt (norm q))
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h)) :
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s =
        normDirichletSeries (angularResidueIdealChar q χ ℓ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s =
        normDirichletSeries (angularResidueIdealChar q (star χ) (-ℓ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) (|(ℓ:ℝ)|/2) root L Ldual ∧
      ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) (|(ℓ:ℝ)|/2) L := by
  have hbase : ‖G/(Real.sqrt (norm q):ℝ)‖ = 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),hG,
      div_self (Real.sqrt_pos.mpr (norm_pos_of_ne_zero hq)).ne']
  obtain ⟨n,rfl | rfl⟩ := Int.eq_nat_or_neg ℓ
  · let root := (G/(Real.sqrt (norm q):ℝ))*(angularConductorPhase q)^n
    have hr : ‖root‖ = 1 := by
      simp only [root,norm_mul,hbase,norm_pow,angularConductorPhase_norm hq,one_pow,mul_one]
    have hFE : ∀ t : ℝ, 0 < t →
        angularLatticeHeat q χ (n:ℤ) (residueHeckeScale q) (|((n:ℤ):ℝ)|/2) (1/t) =
          root*(t:ℂ)*angularLatticeHeat q (star χ) (-(n:ℤ))
            (residueHeckeScale q) (|((n:ℤ):ℝ)|/2) t := by
      intro t ht
      simpa only [Int.cast_natCast,abs_of_nonneg ((Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)))] using
        angularHeat_nat_transformation hq χ G hFourier n ht
    obtain ⟨L,Ldual,hL,hs,hds,hfunctional,horder⟩ :=
      angularHecke_from_heatTransformation hq χ (n:ℤ) hu hn root hr hFE
    exact ⟨root,L,Ldual,hr,hL,hs,hds,hfunctional,horder⟩
  · let root := (G/(Real.sqrt (norm q):ℝ))*(angularConductorPhaseNeg q)^n
    have hr : ‖root‖ = 1 := by
      simp only [root,norm_mul,hbase,norm_pow,angularConductorPhaseNeg_norm hq,one_pow,mul_one]
    have hFE : ∀ t : ℝ, 0 < t →
        angularLatticeHeat q χ (-(n:ℤ)) (residueHeckeScale q) (|(Int.cast (-(n:ℤ)) : ℝ)|/2) (1/t) =
          root*(t:ℂ)*angularLatticeHeat q (star χ) (-(-(n:ℤ)))
            (residueHeckeScale q) (|(Int.cast (-(n:ℤ)) : ℝ)|/2) t := by
      intro t ht
      simpa only [Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg ((Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))),neg_neg] using
        angularHeat_neg_nat_transformation hq χ G hFourier n ht
    obtain ⟨L,Ldual,hL,hs,hds,hfunctional,horder⟩ :=
      angularHecke_from_heatTransformation hq χ (-(n:ℤ)) hu hn root hr hFE
    exact ⟨root,L,Ldual,hr,hL,hs,hds,hfunctional,horder⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perfect codifferent pairing on every Eisenstein residue ring.
Unlike the trace pairing without the different, this includes ramified moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- Unit frequencies satisfy the exact Gauss eigenrelation for every modulus. -/
lemma residueCharacterFourier_unit (q : Eisenstein) (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ) (a : (Residues q)ˣ) :
    residueCharacterFourier q hq χ a =
      (star χ) a * gaussSum χ (residueFourierChar q hq) := by
  unfold residueCharacterFourier
  rw [gaussSum_mulShift_eq]
  rw [MulChar.star_eq_inv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueConductorKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitivity detects the kernel of every proper residue reduction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- Triviality on the reduction kernel constructs a genuine lower conductor. -/
lemma residueCharacter_induces_of_kernel {q d : Eisenstein} (hq : q ≠ 0)
    (hd : d ∣ q) (χ : MulChar (Residues q) ℂ)
    (hker : ∀ u : (Residues q)ˣ,
      Units.map (residueReduction hd).toMonoidHom u = 1 → χ u = 1) :
    ∃ ψ : MulChar (Residues d) ℂ, ResidueCharacterInduces q d χ ψ := by
  let f := Units.map (residueReduction hd).toMonoidHom
  have hk : f.ker ≤ χ.toUnitHom.ker := by
    intro u hu
    apply (MonoidHom.mem_ker).mpr
    apply Units.ext
    exact hker u hu
  let E := MonoidHom.liftOfSurjective f (residueReduction_units_surjective hq hd)
    ⟨χ.toUnitHom,hk⟩
  have hE : E.comp f = χ.toUnitHom := MonoidHom.liftOfRightInverse_comp ..
  refine ⟨MulChar.ofUnitHom E,hd,?_⟩
  intro x hx
  let u := (residue_isUnit_of_isCoprime hx).unit
  have hu : (u : Residues q) = Ideal.Quotient.mk (modulus q) x :=
    IsUnit.unit_spec _
  have he := congrArg (fun H => (H u : ℂ)) hE
  change ((E (f u) : ℂˣ) : ℂ) = χ (u : Residues q) at he
  rw [← MulChar.ofUnitHom_coe] at he
  change (MulChar.ofUnitHom E) (residueReduction hd (u : Residues q)) =
    χ (u : Residues q) at he
  rw [hu,residueReduction_mk] at he
  exact he

/-- A primitive character is nontrivial on each proper reduction kernel. -/
theorem primitiveResidue_nontrivial_kernel {q d : Eisenstein} (hq : q ≠ 0)
    (hd : d ∣ q) (hsmall : normNat d < normNat q)
    (χ : MulChar (Residues q) ℂ) (hχ : PrimitiveResidueCharacter q χ) :
    ∃ u : (Residues q)ˣ, Units.map (residueReduction hd).toMonoidHom u = 1 ∧ χ u ≠ 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨ψ,hψ⟩ := residueCharacter_induces_of_kernel hq hd χ h
  exact (not_le_of_gt hsmall) (hχ d ψ hψ)

/-- A nonunit frequency is fixed by a unit on which a primitive character is
nontrivial. The smaller modulus is the quotient by one common prime factor. -/
lemma primitiveResidue_frequency_stabilizer {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : PrimitiveResidueCharacter q χ)
    (a : Residues q) (ha : ¬ IsUnit a) :
    ∃ u : (Residues q)ˣ, a * (u : Residues q) = a ∧ χ u ≠ 1 := by
  classical
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a
  have hcop : ¬ IsCoprime q r := fun h => ha (residue_isUnit_of_isCoprime h)
  have hrel : ¬ IsRelPrime q r := fun h => hcop h.isCoprime
  rw [UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hq] at hrel
  push Not at hrel
  obtain ⟨p,hpq,hpr,hp⟩ := hrel
  obtain ⟨d,hd⟩ := hpq
  obtain ⟨k,hk⟩ := hpr
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd; exact hq hd
  have hdp : d ∣ q := ⟨p, hd.trans (mul_comm p d)⟩
  have hpN : 1 < normNat p := by
    have hp0 := normNat_ne_zero hp.ne_zero
    have hp1 : normNat p ≠ 1 := by
      intro he
      apply hp.not_isUnit
      apply isUnit_of_norm_eq_one
      rw [← normNat_cast, he, Nat.cast_one]
    omega
  have hsmall : normNat d < normNat q := by
    rw [hd,normNat_mul]
    nlinarith [Nat.pos_of_ne_zero (normNat_ne_zero hd0)]
  obtain ⟨u,hu,hχu⟩ := primitiveResidue_nontrivial_kernel hq hdp hsmall χ hχ
  refine ⟨u,?_,hχu⟩
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : Residues q)
  have hxd : Ideal.Quotient.mk (modulus d) x = 1 := by
    have he := congrArg (fun v : (Residues d)ˣ => (v : Residues d)) hu
    change residueReduction hdp (u : Residues q) = 1 at he
    rw [← hx,residueReduction_mk] at he
    exact he
  have hdx : d ∣ x-1 := by
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change Ideal.Quotient.mk (modulus d) (x-1) = 0
    rw [map_sub,hxd,map_one,sub_self]
  have hdiv : q ∣ r*x-r := by
    obtain ⟨y,hy⟩ := hdx
    refine ⟨k*y,?_⟩
    rw [hd,hk]
    calc
      p*k*x-p*k = p*k*(x-1) := by ring
      _ = p*d*(k*y) := by rw [hy]; ring
  rw [← hx, ← map_mul]
  apply (sub_eq_zero.mp ?_)
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)

/-- The Fourier transform of a primitive residue character vanishes at every
nonunit frequency, including those at ramified factors of the modulus. -/
theorem primitiveResidueFourier_nonunit {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) (a : Residues q) (ha : ¬ IsUnit a) :
    residueCharacterFourier q hq χ a = 0 := by
  obtain ⟨u,hu,hχu⟩ := primitiveResidue_frequency_stabilizer hq χ hχ a ha
  have he := gaussSum_mulShift χ ((residueFourierChar q hq).mulShift a) u
  rw [AddChar.mulShift_mulShift, hu] at he
  exact eq_zero_of_mul_eq_self_left hχu he

/-- The complete Gauss eigenrelation holds with the actual zero extension of
the multiplicative character on nonunits. -/
theorem primitiveResidueFourier_eq {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) (a : Residues q) :
    residueCharacterFourier q hq χ a =
      (star χ) a * gaussSum χ (residueFourierChar q hq) := by
  by_cases ha : IsUnit a
  · obtain ⟨u,rfl⟩ := ha
    exact residueCharacterFourier_unit q hq χ u
  · rw [primitiveResidueFourier_nonunit hq χ hχ a ha, MulChar.map_nonunit _ ha, zero_mul]

/-- Finite Fourier inversion at the unit element. This identity only needs
the additive pairing to be perfect; the ring need not be a field. -/
lemma finite_gauss_fourier_at_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ∑ a : R, gaussSum χ (ψ.mulShift a) * ψ (-a) = Fintype.card R := by
  classical
  simp only [gaussSum, Finset.sum_mul, AddChar.mulShift_apply]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : R, χ x * ∑ a : R, ψ (a*(x-1)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← ψ.map_add_eq_mul]
      congr 2
      ring
    _ = ∑ x : R, χ x * (if x = 1 then (Fintype.card R : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [AddChar.sum_mulShift (x-1) hψ, sub_eq_zero]
      split_ifs <;> simp_all
    _ = Fintype.card R := by simp

/-- Exact square norm of the primitive residue Gauss sum, for arbitrary
nonzero Eisenstein modulus, including prime powers above three. -/
theorem primitiveResidueGauss_mul_conj {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) :
    gaussSum χ (residueFourierChar q hq) *
      star (gaussSum χ (residueFourierChar q hq)) = (normNat q : ℂ) := by
  have hi := finite_gauss_fourier_at_one χ (residueFourierChar q hq)
    (residueFourierChar_isPrimitive q hq)
  change (∑ a : Residues q, residueCharacterFourier q hq χ a *
    residueFourierChar q hq (-a)) = _ at hi
  simp_rw [primitiveResidueFourier_eq hq χ hχ, MulChar.star_apply,
    AddChar.map_neg_eq_conj] at hi
  change (∑ a : Residues q, star (χ a) *
    gaussSum χ (residueFourierChar q hq) * star (residueFourierChar q hq a)) = _ at hi
  have he : (∑ a : Residues q, star (χ a) *
      gaussSum χ (residueFourierChar q hq) * star (residueFourierChar q hq a)) =
      gaussSum χ (residueFourierChar q hq) *
        star (gaussSum χ (residueFourierChar q hq)) := by
    change (∑ a : Residues q, star (χ a) *
      gaussSum χ (residueFourierChar q hq) * star (residueFourierChar q hq a)) =
      gaussSum χ (residueFourierChar q hq) *
        star (∑ a : Residues q, χ a * residueFourierChar q hq a)
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [star_mul]
    ring
  rw [he] at hi
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Nat.card_eq_fintype_card, residues_card hq]

/-- Positive real norm of the primitive Gauss sum. -/
theorem primitiveResidueGauss_norm {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) :
    ‖gaussSum χ (residueFourierChar q hq)‖ = Real.sqrt (normNat q : ℝ) := by
  have hi := congrArg Complex.re (primitiveResidueGauss_mul_conj hq χ hχ)
  have hs : ‖gaussSum χ (residueFourierChar q hq)‖^2 = (normNat q : ℝ) := by
    have hc := Complex.mul_conj' (gaussSum χ (residueFourierChar q hq))
    change gaussSum χ (residueFourierChar q hq) *
      star (gaussSum χ (residueFourierChar q hq)) = _ at hc
    rw [hc] at hi
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.natCast_re] using hi
  rw [← hs, Real.sqrt_sq (_root_.norm_nonneg _)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueFourierBridge
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier coefficient occurring in lattice Poisson is exactly
the Gauss transform for the primitive inverse-different additive character. -/
noncomputable section
namespace CubicFirstMoment

lemma residueFiniteFourier_eq_characterFourier {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ) (h : Eisenstein) :
    residueFiniteFourier q χ h =
      residueCharacterFourier q hq χ (Ideal.Quotient.mk (modulus q) h) := by
  unfold residueFiniteFourier residueCharacterFourier gaussSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro v _
  apply congrArg (fun z : ℂ => χ v*z)
  rw [AddChar.mulShift_apply]
  have hv : v = Ideal.Quotient.mk (modulus q) (residueRepresentative q v) :=
    (residueRepresentative_spec q v).symm
  conv_rhs => rw [hv,←map_mul,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveHeckeProof
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive finite and fixed-angular Hecke continuation derived from
finite Gauss orthogonality and the actual Gaussian Poisson formula. -/
noncomputable section
namespace CubicFirstMoment

private lemma primitive_poisson_gauss_norm {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hp : PrimitiveResidueCharacter q χ) :
    ‖gaussSum χ (residueFourierChar q hq)‖ = Real.sqrt (norm q) := by
  simpa only [normNat_cast] using primitiveResidueGauss_norm hq χ hp

private lemma primitive_poisson_gauss_fourier {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hp : PrimitiveResidueCharacter q χ) (h : Eisenstein) :
    residueFiniteFourier q χ h =
      gaussSum χ (residueFourierChar q hq)*(star χ) (Ideal.Quotient.mk (modulus q) h) := by
  rw [residueFiniteFourier_eq_characterFourier hq χ h,primitiveResidueFourier_eq hq χ hp,mul_comm]

theorem primitiveAngularHeckeInput_proved_oai : PrimitiveAngularHeckeInput := by
  intro ℓ q hq χ hp hu hn
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  exact angularHecke_from_finiteFourier hq χ ℓ hu hn
    (gaussSum χ (residueFourierChar q hq)) (primitive_poisson_gauss_norm hq χ hp)
    (primitive_poisson_gauss_fourier hq χ hp)

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.primitiveAngularHeckeInput_proved_oai := @OAI.CubicFirstMoment.primitiveAngularHeckeInput_proved_oai
