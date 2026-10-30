-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:13:54.605579+00:00
-- url     : https://prove2.me/submissions/337ee8b5-0a48-4ff1-8fa3-39a62de60d63

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A015

section
-- module Solutions.OAIQ096_CM.CubicGram_Coordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral coordinates and finite norm cutoffs in the Eisenstein subring. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeCutoffSum_eq_sum (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum f X = ∑ p ∈ primeCutoff X, f p := by
  unfold primeCutoffSum
  rw [tsum_eq_sum (s := primeCutoff X)]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [mem_primeCutoff.mp hp]
  · intro p hp
    simp only [mem_primeCutoff] at hp
    simp [hp]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique primary associates and canonical prime factorization. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma primaryPrimeFactors_norm_prod {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ∏ p ∈ primaryPrimeFactors n, normNat p = normNat n := by
  calc
    _ = normNat (∏ p ∈ primaryPrimeFactors n, p) := (map_prod normNatHom _ _).symm
    _ = normNat n := congrArg normNat (primaryPrimeFactors_prod hn hs)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

@[simp] theorem primeCutoffSum_add (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p + g p) X =
      primeCutoffSum f X + primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_add_distrib]

@[simp] theorem primeCutoffSum_sub (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p - g p) X =
      primeCutoffSum f X - primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_sub_distrib]

@[simp] theorem primeCutoffSum_const_mul (z : ℂ) (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => z * f p) X = z * primeCutoffSum f X := by
  simp only [primeCutoffSum_eq_sum, Finset.mul_sum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite ordered prime convolutions used in the exceptional moments.
The weights are independent on the prime factors; the squarefree cutoff
is exposed exactly as the repeated-prime discrepancy. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact collection of the ordered tuples by their product. -/
theorem orderedConvolution_sum (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    (χ : Eisenstein → ℂ) :
    (∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b * χ b) =
      ∑ f ∈ Fintype.piFinset S, (∏ i, w i (f i))*χ (∏ i, f i) := by
  unfold orderedConvolution orderedConvolutionSupport
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ b ∈ (Fintype.piFinset S).image (fun f => ∏ i, f i),
        ∑ f ∈ Fintype.piFinset S with (∏ i, f i) = b,
          (∏ i, w i (f i))*χ (∏ i, f i) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro f hf
      rw [(Finset.mem_filter.mp hf).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun f hf => Finset.mem_image_of_mem _ hf) _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedAbel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth weighting of prime-character sums

Partial summation applies the
published unweighted Hecke prime estimate to independently specified
smooth prime weights. It also retains the derivative cost of a norm twist.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

/-- Complex partial summation with an explicit bound for the cumulative
coefficients. The right side records endpoint values and total variation. -/
theorem weighted_abel_bound (c : ℕ → ℂ) (f : ℝ → ℂ)
    {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hderiv : IntegrableOn (deriv f) (Set.Icc a b))
    (hc : ∀ t ∈ Set.Icc a b, ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ H) :
    ‖∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k‖ ≤
      H * (‖f a‖ + ‖f b‖ + ∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  let S : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
  have hSa : ‖S a‖ ≤ H := hc a ⟨le_rfl, hab⟩
  have hSb : ‖S b‖ ≤ H := hc b ⟨hab, le_rfl⟩
  have hp : IntegrableOn (fun t => deriv f t * S t) (Set.Ioc a b) :=
    (integrableOn_mul_sum_Icc c ha hderiv).mono_set Set.Ioc_subset_Icc_self
  have hd0 : IntegrableOn (fun t => H * ‖deriv f t‖) (Set.Icc a b) :=
    hderiv.norm.const_mul H
  have hd : IntegrableOn (fun t => H * ‖deriv f t‖) (Set.Ioc a b) :=
    hd0.mono_set Set.Ioc_subset_Icc_self
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖deriv f t * S t‖ ≤ H * ‖deriv f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, mul_comm H]
    exact mul_le_mul_of_nonneg_left (hc t (Set.Ioc_subset_Icc_self ht))
      (_root_.norm_nonneg _)
  have hIntegral : ‖∫ t in Set.Ioc a b, deriv f t * S t‖ ≤
      H * ∫ t in Set.Ioc a b, ‖deriv f t‖ := by
    calc
      _ ≤ ∫ t in Set.Ioc a b, ‖deriv f t * S t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc a b, H * ‖deriv f t‖ := integral_mono_ae hp.norm hd hpoint
      _ = _ := integral_const_mul H _
  rw [sum_mul_eq_sub_sub_integral_mul c ha hab hdiff hderiv]
  change ‖f b * S b - f a * S a - ∫ t in Set.Ioc a b, deriv f t * S t‖ ≤ _
  calc
    _ ≤ ‖f b * S b - f a * S a‖ + ‖∫ t in Set.Ioc a b, deriv f t * S t‖ :=
      norm_sub_le _ _
    _ ≤ (‖f b * S b‖ + ‖f a * S a‖) +
        H * ∫ t in Set.Ioc a b, ‖deriv f t‖ :=
      add_le_add (norm_sub_le _ _) hIntegral
    _ ≤ (‖f b‖ * H + ‖f a‖ * H) +
        H * ∫ t in Set.Ioc a b, ‖deriv f t‖ := by
      simp only [norm_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hSb (_root_.norm_nonneg _))
        (mul_le_mul_of_nonneg_left hSa (_root_.norm_nonneg _))) le_rfl
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedPrimeInput
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published prime input to smooth prime weights

Prime elements of equal norm are collected without identifying conjugate
prime ideals. Complex Abel summation then derives the smooth-weighted
estimate from `CubicPrimeSiegelWalfisz`. The weighted estimate follows by partial summation.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

lemma primeNormCoefficient_cumulative (R t : ℝ) (χ : Eisenstein → ℂ)
    (ht : 0 ≤ t) (htR : t ≤ R) :
    (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeNormCoefficient R χ n) = primeCutoffSum χ t := by
  simp only [primeNormCoefficient]
  rw [Finset.sum_comm, primeCutoffSum_eq_sum]
  have he (p : Eisenstein) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, if n = normNat p then χ p else 0) =
        if norm p ≤ t then χ p else 0 := by
    simp only [Finset.sum_ite_eq', Finset.mem_Icc, Nat.zero_le, true_and]
    simp only [Nat.le_floor_iff ht, normNat_cast]
  simp_rw [he]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, mem_primeCutoff]
  constructor
  · intro hp
    exact ⟨hp.1.1, hp.2⟩
  · intro hp
    exact ⟨⟨hp.1, hp.2.trans htR⟩, hp.2⟩

lemma primeNormCoefficient_weighted (a b : ℝ) (f : ℝ → ℂ) (χ : Eisenstein → ℂ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * primeNormCoefficient b χ n) =
      ∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p) * χ p := by
  simp only [primeNormCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : normNat p ≤ ⌊b⌋₊ := (Nat.le_floor_iff (ha.trans hab)).mpr
    (by rw [normNat_cast]; exact (mem_primeCutoff.mp hp).2)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_Ioc, hpb, and_true]
  simp only [Nat.floor_lt ha, normNat_cast]

/-- Weighted interval sums inherit a uniform bound for all their unweighted
prime prefixes, at the explicit cost of total variation of the weight. -/
theorem weighted_prime_bound (χ : Eisenstein → ℂ) (f : ℝ → ℂ)
    {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hderiv : IntegrableOn (deriv f) (Set.Icc a b))
    (hχ : ∀ t ∈ Set.Icc a b, ‖primeCutoffSum χ t‖ ≤ H) :
    ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p) * χ p‖ ≤
      H * (‖f a‖ + ‖f b‖ + ∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  rw [← primeNormCoefficient_weighted a b f χ ha hab]
  apply weighted_abel_bound (primeNormCoefficient b χ) f ha hab hdiff hderiv
  intro t ht
  rw [primeNormCoefficient_cumulative b t χ (ha.trans ht.1) ht.2]
  exact hχ t ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem hasDerivAt_mellinPhase (u : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (mellinPhase u)
      (mellinPhase u x * ((u / x : ℝ) : ℂ) * Complex.I) x := by
  have h := (((Real.hasDerivAt_log hx).const_mul u).ofReal_comp.mul_const Complex.I).cexp
  unfold mellinPhase
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

theorem hasDerivAt_weighted_mellinPhase {w : ℝ → ℂ} {w' : ℂ} {x : ℝ}
    (hw : HasDerivAt w w' x) (u : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => w t * mellinPhase u t)
      (w' * mellinPhase u x + w x * (mellinPhase u x * ((u / x : ℝ) : ℂ) * Complex.I)) x :=
  hw.mul (hasDerivAt_mellinPhase u hx)

/-- The derivative loss is linear in the Mellin height and inversely
proportional to the norm variable. -/
theorem norm_deriv_weighted_mellinPhase {w : ℝ → ℂ} {w' : ℂ} {x : ℝ}
    (hw : HasDerivAt w w' x) (u : ℝ) (hx : 0 < x) :
    ‖deriv (fun t => w t * mellinPhase u t) x‖ ≤
      ‖w'‖ + ‖w x‖ * (|u| / x) := by
  rw [(hasDerivAt_weighted_mellinPhase hw u hx.ne').deriv]
  calc
    _ ≤ ‖w' * mellinPhase u x‖ +
        ‖w x * (mellinPhase u x * ((u / x : ℝ) : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = _ := by
      simp only [norm_mul, mellinPhase_norm, Complex.norm_I, mul_one, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hx]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative fixed-angular Hecke prime estimates

The published input is the degree-two, nonexceptional specialization of
Kaneko--Thorner, *Highly uniform prime number theorems*, Ann. Inst. Fourier
75 (2025), Theorem 1.2, pp. 1904--1905 (restating Iwaniec--Kowalski,
Theorem 5.13), with the zero-free region and completion from Rajan (1998),
Proposition 1 and Section 1. The exponential conductor-dependent error
is retained. Arbitrary logarithmic savings are derived below; they are
not included among the published-input hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CubicFirstMoment

private lemma eventually_loglog_small (a b ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      a + b * Real.log (Real.log x) ≤ ε * Real.sqrt (Real.log x) := by
  have hlim : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hc : (fun _ : ℝ => a) =o[atTop] (fun x => Real.sqrt (Real.log x)) := by
    apply isLittleO_const_left.mpr
    right
    simpa only [Function.comp_def, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hlim
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    Real.tendsto_log_atTop
  have hl' : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
      (fun x => Real.sqrt (Real.log x)) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using hl
  have h := (hc.add (hl'.const_mul_left b)).def hε
  filter_upwards [h] with x hx
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hx)

/-- Logarithmic conductor growth makes the published exponential error
smaller than any prescribed logarithmic saving, uniformly in the conductor. -/
lemma heckeExponentialError_logSaving {c K A D : ℝ}
    (hc : 0 < c) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, ∀ Q : ℝ, 1 ≤ Q → Q ≤ K * (Real.log x) ^ A →
      heckeExponentialError c x Q ≤ 16 * x / (Real.log x) ^ D := by
  have hcond := eventually_loglog_small (Real.log K) A 1 zero_lt_one
  have hdecay := eventually_loglog_small 0 (D + 4) (c / 2) (by positivity)
  filter_upwards [hcond, hdecay, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hcond hdecay hL hx Q hQ hQmax
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hL₀ : 0 < Real.log x := Real.log_pos hx
  have hQ₀ : 0 < Q := zero_lt_one.trans_le hQ
  have hlogQ₀ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogQ : Real.log Q ≤ Real.sqrt (Real.log x) := by
    have h := Real.log_le_log hQ₀ hQmax
    rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hL₀ A).ne', Real.log_rpow hL₀] at h
    exact h.trans (by simpa only [one_mul] using hcond)
  have hroot : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hL₀
  have hd : 0 < Real.log Q + Real.sqrt (Real.log x) := by positivity
  have hratio : Real.sqrt (Real.log x) / 2 ≤
      Real.log x / (Real.log Q + Real.sqrt (Real.log x)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [Real.sq_sqrt hL₀.le]
  have he₁ : Real.exp (-c * Real.log x / (Real.log Q + Real.sqrt (Real.log x))) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = -c * (Real.log x / (Real.log Q + Real.sqrt (Real.log x))) := by ring
      _ ≤ _ := by nlinarith
  have he₂ : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤
      (Real.log x) ^ (-(D + 4)) := by
    rw [Real.rpow_def_of_pos hL₀]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlogprod : Real.log (x * Q) ≤ 2 * Real.log x := by
    rw [Real.log_mul hx₀.ne' hQ₀.ne']
    have hq := hlogQ.trans (Real.sqrt_le_self_iff.mpr (Or.inr hL))
    linarith
  have hpoly : (Real.log (x * Q)) ^ 4 ≤ 16 * (Real.log x) ^ 4 := by
    calc
      _ ≤ (2 * Real.log x) ^ 4 := by
        gcongr
        exact Real.log_nonneg (by nlinarith)
      _ = _ := by ring
  have hpow : (Real.log x) ^ 4 * (Real.log x) ^ (-(D + 4)) =
      1 / (Real.log x) ^ D := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL₀]
    norm_num
    rw [Real.rpow_neg hL₀.le]
  calc
    heckeExponentialError c x Q ≤
        x * (16 * (Real.log x) ^ 4) * (Real.log x) ^ (-(D + 4)) := by
      unfold heckeExponentialError
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly hx₀.le)
        (he₁.trans he₂) (Real.exp_nonneg _) (by positivity)
    _ = 16 * x / (Real.log x) ^ D := by rw [mul_assoc, mul_assoc, hpow]; ring

/-- The prime-power deletion error is also negligible at every fixed
logarithmic scale. -/
lemma sqrt_logSq_logSaving (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x * (Real.log x) ^ 2 ≤ x / (Real.log x) ^ D := by
  have h := (isLittleO_log_rpow_rpow_atTop (D + 2)
    (by norm_num : (0 : ℝ) < 1 / 2)).def zero_lt_one
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  have hx₀ : 0 < x := zero_lt_one.trans hx₁
  have hL₀ : 0 < Real.log x := Real.log_pos hx₁
  have hsmall : (Real.log x) ^ (D + 2) ≤ Real.sqrt x := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hL₀.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _), one_mul, Real.sqrt_eq_rpow] using hx
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL₀ D)).mpr
  calc
    _ = Real.sqrt x * (Real.log x) ^ (D + 2) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hL₀]
      congr 2
      ring
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt hx₀.le

lemma angularConductorFactor_ge_one (ℓ : ℤ) : 1 ≤ angularConductorFactor ℓ := by
  unfold angularConductorFactor
  nlinarith [abs_nonneg (ℓ : ℝ)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAngularKummerPrime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-angular prime estimates for the literal ramified numerator

This is the nonexceptional degree-two specialization of Kaneko--Thorner,
*Highly uniform prime number theorems*, Ann. Inst. Fourier 75 (2025),
Theorem 1.2, pp.1904--1905 (Iwaniec--Kowalski, Theorem 5.13), with the
fixed-type zero-free region of Rajan (1998), Proposition 1 and Section 1.
The finite character is `cubicNumeratorChar` of modulus `9*v`; its
identification on primary elements is proved from
`CubicSupplementaryPeriodicity` in `CubicNumeratorCharacter`.

The analytic conductor majorant is
`3 * N(9*v) * (|ell|/2+3) * (|ell|/2+4)`:
`N(9*v)=81*N(v)`, so its constant is 243. The nonzero angular type
excludes a principal/exceptional-real character. The raw input below
retains the exponential conductor error and the prime-power deletion
term. Logarithmic and weighted estimates are deductions, not inputs.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma angularKummerConductorFactor_ge_one (ℓ : ℤ) :
    1 ≤ angularKummerConductorFactor ℓ := by
  have h := angularConductorFactor_ge_one ℓ
  unfold angularKummerConductorFactor
  linarith

lemma angularKummerAnalyticConductor_ge_one (ℓ : ℤ) {v : Eisenstein}
    (hv : v ≠ 0) : 1 ≤ angularKummerAnalyticConductor ℓ v := by
  have hn : (1:ℝ) ≤ norm v := by
    rw [←normNat_cast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero hv)
  unfold angularKummerAnalyticConductor
  nlinarith [angularKummerConductorFactor_ge_one ℓ]

theorem angular_kummer_chebyshev_logSaving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (_hA : 0 < A) (_hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ x : ℝ, X₀ ≤ x → ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
        norm v ≤ (Real.log x) ^ A →
        ‖primeChebyshev (angularKummerCharacter ℓ v) x‖ ≤ C * x / (Real.log x) ^ D := by
  obtain ⟨B, c, hB, hc, hbound⟩ := hEF ℓ hℓ
  have hK : 0 < angularKummerConductorFactor ℓ := zero_lt_one.trans_le (angularKummerConductorFactor_ge_one ℓ)
  have herr := heckeExponentialError_logSaving (K := angularKummerConductorFactor ℓ)
    (A := A) (D := D) hc hK
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (herr.and (sqrt_logSq_logSaving D))
  refine ⟨17 * B, max X₁ 3, by positivity, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx v hv hnc hcon
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx₃ : 3 ≤ x := (le_max_right _ _).trans hx
  have he := (hX₁ x hx₁).1 (angularKummerAnalyticConductor ℓ v)
    (angularKummerAnalyticConductor_ge_one ℓ hv)
    (mul_le_mul_of_nonneg_left hcon hK.le)
  calc
    _ ≤ B * (16 * x / (Real.log x) ^ D + x / (Real.log x) ^ D) :=
      (hbound v hv hnc x hx₃).trans
        (mul_le_mul_of_nonneg_left (add_le_add he (hX₁ x hx₁).2) hB.le)
    _ = _ := by ring

/-- Partial summation removes the logarithmic prime weight, permitting
smooth weights and norm phases. The derivative cost is retained exactly. -/
theorem weighted_angular_kummer_prime_log_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ a b : ℝ, X₀ ≤ a → a ≤ b → ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
        norm v ≤ (Real.log a) ^ A → ∀ f : ℝ → ℂ,
          (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t => f t / (Real.log t : ℂ)) t) →
          IntegrableOn (deriv (fun t => f t / (Real.log t : ℂ))) (Set.Icc a b) →
          ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
            f (norm p) * angularKummerCharacter ℓ v p‖ ≤
          (C * b / (Real.log a) ^ D) *
            (‖f a / (Real.log a : ℂ)‖ + ‖f b / (Real.log b : ℂ)‖ +
              ∫ t in Set.Ioc a b, ‖deriv (fun t => f t / (Real.log t : ℂ)) t‖) := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := angular_kummer_chebyshev_logSaving hEF ℓ hℓ A D hA hD
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro a b ha hab v hv hnc hcon f hdiff hderiv
  have ha₁ : 1 < a := hX₀.trans_le ha
  have ha₀ : 0 < a := zero_lt_one.trans ha₁
  have hprefix : ∀ t ∈ Set.Icc a b,
      ‖primeCutoffSum (fun p => angularKummerCharacter ℓ v p * (Real.log (norm p) : ℂ)) t‖ ≤
        C * b / (Real.log a) ^ D := by
    intro t ht
    have ht₀ : 0 < t := ha₀.trans_le ht.1
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha₀ ht.1
    have hcon' : norm v ≤ (Real.log t) ^ A :=
      hcon.trans (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hA.le)
    apply (hbound t (ha.trans ht.1) v hv hnc hcon').trans
    exact div_le_div₀ (mul_nonneg hC.le (ht₀.le.trans ht.2))
      (mul_le_mul_of_nonneg_left ht.2 hC.le)
      (Real.rpow_pos_of_pos (Real.log_pos ha₁) D)
      (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hD.le)
  have h := weighted_prime_bound
    (fun p => angularKummerCharacter ℓ v p * (Real.log (norm p) : ℂ))
    (fun t => f t / (Real.log t : ℂ)) ha₀.le hab hdiff hderiv hprefix
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p hp
  have hp₁ : 1 < norm p := ha₁.trans (Finset.mem_filter.mp hp).2
  have hlog : (Real.log (norm p) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hp₁).ne'
  field_simp


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularKummerPrimeSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw angular Chebyshev estimate implies the ordinary prime
Siegel--Walfisz bound. A square-root initial segment is bounded directly;
partial summation on the remaining interval has bounded reciprocal-log
variation. -/
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma reciprocal_log_variation {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    (∀ t ∈ Icc a b, DifferentiableAt ℝ (fun t => (1:ℂ)/(Real.log t:ℂ)) t) ∧
    IntegrableOn (deriv (fun t => (1:ℂ)/(Real.log t:ℂ))) (Icc a b) ∧
    ‖(1:ℂ)/(Real.log a:ℂ)‖+‖(1:ℂ)/(Real.log b:ℂ)‖+
      (∫ t in Ioc a b, ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖) ≤ 3 := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le ha
  have hla : 1 ≤ Real.log a := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ha
  let f : ℝ → ℝ := fun t => 1/Real.log t
  let g : ℝ → ℝ := fun t => -(t⁻¹)/(Real.log t)^2
  have hder (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt f (g t) t := by
    convert! (hasDerivAt_const t (1:ℝ)).div
      (Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))))
      (Real.log_pos (ha1.trans_le ht.1)).ne' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g,zero_mul,one_mul,zero_sub]
  have hg : ContinuousOn g (Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))
    have hlt : Real.log t ≠ 0 := (Real.log_pos (ha1.trans_le ht.1)).ne'
    exact ((continuousAt_id.inv₀ ht0).neg.div ((Real.continuousAt_log ht0).pow 2)
      (pow_ne_zero 2 hlt)).continuousWithinAt
  have he (t : ℝ) (ht : t ∈ Icc a b) :
      deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t = (g t:ℂ) := by
    convert (hder t ht).ofReal_comp.deriv using 1
    all_goals try with_reducible_and_instances rfl
    simp only [f,Complex.ofReal_div,Complex.ofReal_one]
  have hi : IntegrableOn (deriv (fun t => (1:ℂ)/(Real.log t:ℂ))) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hg).integrableOn_Icc.congr_fun
      (fun t ht => (he t ht).symm) measurableSet_Icc
  have hint : (∫ t in Ioc a b, ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖) =
      f a-f b := by
    have hn (t : ℝ) (ht : t ∈ Icc a b) :
        ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖ = -g t := by
      rw [he t ht,Complex.norm_real,Real.norm_of_nonpos]
      change -t⁻¹/(Real.log t)^2 ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr
        (zero_lt_one.trans (ha1.trans_le ht.1)).le)) (sq_nonneg _)
    rw [←intervalIntegral.integral_of_le hab]
    have hc : (∫ t in a..b, ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖) =
        ∫ t in a..b, -g t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact hn t ht
    rw [hc,intervalIntegral.integral_neg]
    have hf : (∫ t in a..b, g t) = f b-f a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hg.intervalIntegrable_of_Icc hab)
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact hder t ht
    rw [hf]
    ring
  refine ⟨?_,hi,?_⟩
  · intro t ht
    simpa only [f,Complex.ofReal_div,Complex.ofReal_one] using
      (hder t ht).ofReal_comp.differentiableAt
  · have hlb : 1 ≤ Real.log b := hla.trans (Real.log_le_log
      (zero_lt_one.trans ha1) hab)
    rw [hint,norm_div,norm_div,norm_one,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (zero_le_one.trans hla),Real.norm_of_nonneg (zero_le_one.trans hlb)]
    have hfa : f a ≤ 1 := by
      simpa only [f,div_one] using one_div_le_one_div_of_le zero_lt_one hla
    have hfb : 0 ≤ f b := by dsimp [f]; positivity
    dsimp [f] at *
    linarith

lemma angularKummerCharacter_norm_le_one (ℓ : ℤ) (v : Eisenstein)
    {p : Eisenstein} (hp : primary p) : ‖angularKummerCharacter ℓ v p‖ ≤ 1 := by
  rw [angularKummerCharacter,norm_mul,norm_theta (primary_ne_zero hp),one_mul]
  exact norm_cubicSymbol_le_one hp v

/-- The unweighted prime estimate is derived from the raw published
Chebyshev error; it is not an additional analytic input. -/
theorem angular_kummer_prime_logSaving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A →
      ‖primeCutoffSum (angularKummerCharacter ℓ v) X‖ ≤ C*X/(Real.log X)^D := by
  obtain ⟨C,Y₀,hC,hY₀,hbound⟩ := weighted_angular_kummer_prime_log_bound hEF ℓ hℓ
    (2*A) (2*D) (by positivity) (by positivity)
  have hroot := Real.tendsto_sqrt_atTop.eventually_ge_atTop (max Y₀ (Real.exp 1))
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp
    (((hroot.and (sqrt_logSq_logSaving D)).and
      (Real.tendsto_log_atTop.eventually_ge_atTop 4)).and (eventually_gt_atTop (1:ℝ)))
  refine ⟨18+3*C,max X₀ 2,by positivity,by simp,?_⟩
  intro X hX v hv hnc hNv
  obtain ⟨⟨⟨hr,hs⟩,hlog⟩,hX1⟩ := hX₀ X ((le_max_left _ _).trans hX)
  have hXp : 0 < X := zero_lt_one.trans hX1
  have hLp : 0 < Real.log X := by linarith
  have hsp : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXp
  have hsY : Y₀ ≤ Real.sqrt X := (le_max_left _ _).trans hr
  have hse : Real.exp 1 ≤ Real.sqrt X := (le_max_right _ _).trans hr
  have hsX : Real.sqrt X ≤ X := Real.sqrt_le_self_iff.mpr (Or.inr hX1.le)
  have hls : Real.log (Real.sqrt X) = Real.log X/2 := Real.log_sqrt hXp.le
  have hls1 : 1 ≤ Real.log (Real.sqrt X) := by rw [hls]; linarith
  have hbase : Real.log X ≤ (Real.log (Real.sqrt X))^2 := by rw [hls]; nlinarith
  have hpow (E : ℝ) (hE : 0 ≤ E) : (Real.log X)^E ≤ (Real.log (Real.sqrt X))^(2*E) := by
    calc
      _ ≤ ((Real.log (Real.sqrt X))^2)^E := Real.rpow_le_rpow hLp.le hbase hE
      _ = _ := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_natCast_mul (zero_le_one.trans hls1) 2 E).symm
  have hcon : norm v ≤ (Real.log (Real.sqrt X))^(2*A) := hNv.trans (hpow A hA.le)
  obtain ⟨hd,hi,hvar⟩ := reciprocal_log_variation hse hsX
  have hlarge := hbound (Real.sqrt X) X hsY hsX v hv hnc hcon (fun _ => 1) hd hi
  have hbig : ‖∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p),
      angularKummerCharacter ℓ v p‖ ≤ 3*C*X/(Real.log X)^D := by
    simp only [one_mul] at hlarge
    apply hlarge.trans
    calc
      _ ≤ (C*X/(Real.log (Real.sqrt X))^(2*D))*3 :=
        mul_le_mul_of_nonneg_left hvar (by positivity)
      _ ≤ (C*X/(Real.log X)^D)*3 :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity)
            (Real.rpow_pos_of_pos hLp D) (hpow D hD.le)) (by norm_num)
      _ = _ := by ring
  have hsmall : ‖primeCutoffSum (angularKummerCharacter ℓ v) (Real.sqrt X)‖ ≤
      18*X/(Real.log X)^D := by
    rw [primeCutoffSum_eq_sum]
    have hcard := primary_support_card_le (primeCutoff (Real.sqrt X)) hsp.le
      (fun p hp => ⟨(mem_primeCutoff.mp hp).1.1,(mem_primeCutoff.mp hp).2⟩)
    have hsq : Real.sqrt X ≤ X/(Real.log X)^D := by
      have hx : Real.sqrt X ≤ Real.sqrt X*(Real.log X)^2 :=
        le_mul_of_one_le_right hsp.le (one_le_pow₀ (by linarith))
      exact hx.trans hs
    calc
      _ ≤ ∑ _p ∈ primeCutoff (Real.sqrt X), (1:ℝ) := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun p hp => angularKummerCharacter_norm_le_one ℓ v
          (mem_primeCutoff.mp hp).1.1)
      _ = ((primeCutoff (Real.sqrt X)).card:ℝ) := by simp
      _ ≤ 18*Real.sqrt X := hcard
      _ ≤ 18*(X/(Real.log X)^D) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = _ := by ring
  have hsplit : primeCutoffSum (angularKummerCharacter ℓ v) X =
      primeCutoffSum (angularKummerCharacter ℓ v) (Real.sqrt X)+
        ∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p),
          angularKummerCharacter ℓ v p := by
    rw [primeCutoffSum_eq_sum,primeCutoffSum_eq_sum]
    have he : (primeCutoff X).filter (fun p => ¬Real.sqrt X < norm p) =
        primeCutoff (Real.sqrt X) := by
      ext p
      simp only [Finset.mem_filter,mem_primeCutoff,not_lt]
      constructor
      · rintro ⟨⟨hp,_⟩,hs⟩; exact ⟨hp,hs⟩
      · rintro ⟨hp,hs⟩; exact ⟨⟨hp,hs.trans hsX⟩,hs⟩
    rw [←he]
    exact (Finset.sum_filter_add_sum_filter_not (primeCutoff X)
      (fun p => Real.sqrt X < norm p) _).symm.trans (add_comm _ _)
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hsmall hbig).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularKummerAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal angular cubic character, with the argument order of the
cubic residue symbol. Only multiplicativity in the prime variable is used;
the fixed angular factor is not duplicated in the numerator variable. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma angularCubicSymbol_mul_lower (ℓ : ℤ) {a b : Eisenstein}
    (ha : a ≠ 0) (hb : b ≠ 0) (v : Eisenstein) :
    angularCubicSymbol ℓ (a*b) v = angularCubicSymbol ℓ a v*angularCubicSymbol ℓ b v := by
  simp only [angularCubicSymbol,angularKummerCharacter,theta_mul,
    cubicSymbol_mul_lower ha hb]
  ring

lemma angularCubicSymbol_norm_le_one (ℓ : ℤ) {a : Eisenstein}
    (ha : primary a) (v : Eisenstein) : ‖angularCubicSymbol ℓ a v‖ ≤ 1 :=
  angularKummerCharacter_norm_le_one ℓ v ha

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongPrimeSW
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-angular weighted and long-interval prime bounds derived from
`AngularKummerPrimeExplicitEstimate`. The surviving angular character is
literal, and the interval may begin at exp(sqrt(log X)). -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem weighted_angular_kummer_prime_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ a b : ℝ, X₀ ≤ a → a ≤ b →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log a)^A → ∀ f : ℝ → ℂ,
      (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) →
      IntegrableOn (deriv f) (Set.Icc a b) →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p)*angularKummerCharacter ℓ v p‖ ≤
        (C*b/(Real.log a)^D)*(‖f a‖+‖f b‖+∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := angular_kummer_prime_logSaving hEF ℓ hℓ A D hA hD
  refine ⟨C,X₀,hC,hX₀,?_⟩
  intro a b ha hab v hv hn hcon f hdiff hderiv
  have ha1 : 1 < a := hX₀.trans_le ha
  have ha0 : 0 < a := zero_lt_one.trans ha1
  apply weighted_prime_bound (fun p => angularKummerCharacter ℓ v p) f ha0.le hab hdiff hderiv
  intro t ht
  have hat := Real.log_le_log ha0 ht.1
  have ht0 : 0 < t := ha0.trans_le ht.1
  have hc : norm v ≤ (Real.log t)^A := hcon.trans
    (Real.rpow_le_rpow (Real.log_pos ha1).le hat hA.le)
  apply (hbound t (ha.trans ht.1) v hv hn hc).trans
  exact div_le_div₀ (mul_nonneg hC.le (ht0.le.trans ht.2))
    (mul_le_mul_of_nonneg_left ht.2 hC.le)
    (Real.rpow_pos_of_pos (Real.log_pos ha1) D)
    (Real.rpow_le_rpow (Real.log_pos ha1).le hat hD.le)

/-- The precise raw Kummer prime input, followed by partial summation,
gives arbitrary T-power saving on every interval above a prime scale P
as soon as T <= (log P)^2. Smooth weights retain their actual variation. -/
theorem angular_long_prime_interval_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P R a b : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 → P ≤ a → a ≤ b → b ≤ R*P →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ∀ f : ℝ → ℂ, (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) →
      IntegrableOn (deriv f) (Set.Icc a b) →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p)*angularKummerCharacter ℓ v p‖ ≤
        (C*(R*P)/T^D)*(‖f a‖+‖f b‖+∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := weighted_angular_kummer_prime_bound hEF ℓ hℓ
    (2*A) (2*D) (by positivity) (by positivity)
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro T P R a b hT hP hTP hPa hab hb v hv hnc hcon f hdiff hint
  have hP1 : 1 < P := hP₀.trans_le hP
  have hP0 : 0 < P := zero_lt_one.trans hP1
  have ha0 : 0 < a := hP0.trans_le hPa
  have hb0 : 0 < b := ha0.trans_le hab
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hloga : Real.log P ≤ Real.log a := Real.log_le_log hP0 hPa
  have hsquare (E : ℝ) : ((Real.log P)^2)^E = (Real.log P)^(2*E) := by
    simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hlogP.le 2 E).symm
  have hcon' : norm v ≤ (Real.log a)^(2*A) := by
    calc
      _ ≤ T^A := hcon
      _ ≤ ((Real.log P)^2)^A := Real.rpow_le_rpow hT0.le hTP hA.le
      _ = (Real.log P)^(2*A) := hsquare A
      _ ≤ (Real.log a)^(2*A) := Real.rpow_le_rpow hlogP.le hloga (by positivity)
  have hden : T^D ≤ (Real.log a)^(2*D) := by
    calc
      _ ≤ ((Real.log P)^2)^D := Real.rpow_le_rpow hT0.le hTP hD.le
      _ = (Real.log P)^(2*D) := hsquare D
      _ ≤ (Real.log a)^(2*D) := Real.rpow_le_rpow hlogP.le hloga (by positivity)
  have hfrac : C*b/(Real.log a)^(2*D) ≤ C*(R*P)/T^D :=
    div_le_div₀ (mul_nonneg hC.le (hb0.le.trans hb)) (mul_le_mul_of_nonneg_left hb hC.le)
      (Real.rpow_pos_of_pos hT0 D) hden
  apply (hbound a b (hP.trans hPa) hab v hv hnc hcon' f hdiff hint).trans
  apply mul_le_mul_of_nonneg_right hfrac
  exact add_nonneg (add_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    (integral_nonneg (fun _ => _root_.norm_nonneg _))


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeWeightVariation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete total-variation control for rescaled prime weights and their
Mellin twists. This is the cost in the proved Abel summation inequality. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma contDiffOn_rescaled_mellin {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) (Y u : ℝ) :
    ContDiffOn ℝ ∞ (fun t => w (t/Y)*mellinPhase u t) (Ioi 0) := by
  intro x hx
  have hl : ContDiffAt ℝ ∞ (fun t : ℝ => u*Real.log t) x :=
    contDiffAt_const.mul (Real.contDiffAt_log.mpr (ne_of_gt hx))
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => ((u*Real.log t:ℝ):ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
  have hw' : ContDiff ℝ ∞ (fun t : ℝ => w (t/Y)) := hw.comp (contDiff_id.div_const Y)
  exact (hw'.contDiffAt.mul (hc.mul contDiffAt_const).cexp).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primeDetectorCutoff_one {x : ℝ} (hx : x ≤ 1) : primeDetectorCutoff x = 1 := by
  rw [primeDetectorCutoff,Real.smoothTransition.zero_of_nonpos (by linarith),sub_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCutoffDerivative
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete detector has a uniformly bounded radial derivative.
This supplies the actual variation cost when one prime is left free in
the stopped coefficient; it is not a sequence-cancellation assumption. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma primeDetectorCutoff_deriv_zero {x : ℝ} (hx : x ∉ Icc (1:ℝ) 2) :
    deriv primeDetectorCutoff x = 0 := by
  by_cases hlo : x < 1
  · have he : EqOn primeDetectorCutoff (fun _ : ℝ => (1:ℝ)) (Iio 1) :=
      fun y hy => primeDetectorCutoff_one hy.le
    simpa only [deriv_const] using he.deriv isOpen_Iio hlo
  · have hhi : 2 < x := by
      have h := not_and_or.mp hx
      rcases h with h | h
      · exact False.elim (h (le_of_not_gt hlo))
      · exact lt_of_not_ge h
    have he : EqOn primeDetectorCutoff (fun _ : ℝ => (0:ℝ)) (Ioi 2) :=
      fun y hy => primeDetectorCutoff_zero hy.le
    simpa only [deriv_const] using he.deriv isOpen_Ioi hhi

theorem primeDetectorCutoff_radial_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ D := by
  have hd : Continuous (deriv primeDetectorCutoff) :=
    primeDetectorCutoff_smooth.continuous_deriv (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((hd.norm.mul continuous_id).continuousOn)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x hx
  by_cases hmem : x ∈ Icc (1:ℝ) 2
  · have h := hD x hmem
    change ‖‖deriv primeDetectorCutoff x‖*x‖ ≤ D at h
    have hn : 0 ≤ ‖deriv primeDetectorCutoff x‖*x := mul_nonneg (_root_.norm_nonneg _) hx.le
    rw [Real.norm_eq_abs,abs_of_nonneg hn] at h
    simpa only [Real.norm_eq_abs] using h.trans (le_max_left D 0)
  · rw [primeDetectorCutoff_deriv_zero hmem,abs_zero,zero_mul]
    exact le_max_right _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cutoff weights on a free long prime. Their variation depends
on its dyadic ratio and Mellin height, not on the cutoff scales. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma radial_mellin_interval_variation {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    {P R a b M D : ℝ} (hP : 0 < P) (_hR : 1 ≤ R) (ha : P ≤ a)
    (hab : a ≤ b) (hb : b ≤ R*P) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hwm : ∀ x, ‖w x‖ ≤ M) (hwd : ∀ x, 0 < x → ‖deriv w x‖*x ≤ D) (u : ℝ) :
    let f := fun t => w t*mellinPhase u t
    (∀ t ∈ Icc a b, DifferentiableAt ℝ f t) ∧
    IntegrableOn (deriv f) (Icc a b) ∧
    ‖f a‖+‖f b‖+(∫ t in Ioc a b, ‖deriv f t‖) ≤
      2*M+(R-1)*(D+M*|u|) := by
  dsimp only
  have hsub : Icc a b ⊆ Ioi (0:ℝ) := fun _ ht => hP.trans_le (ha.trans ht.1)
  have hs : ContDiffOn ℝ ∞ (fun t => w t*mellinPhase u t) (Ioi 0) := by
    simpa only [div_one] using contDiffOn_rescaled_mellin hw 1 u
  have hd : ContinuousOn (deriv (fun t => w t*mellinPhase u t)) (Icc a b) :=
    (hs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  refine ⟨?_,hd.integrableOn_Icc,?_⟩
  · intro t ht
    exact ((hs t (hsub ht)).contDiffAt (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt
      (by norm_num)
  have hpoint (t : ℝ) (ht : t ∈ uIoc a b) :
      ‖‖deriv (fun t => w t*mellinPhase u t) t‖‖ ≤ (D+M*|u|)/P := by
    rw [uIoc_of_le hab] at ht
    have htP : P ≤ t := ha.trans ht.1.le
    have ht0 : 0 < t := hP.trans_le htP
    rw [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
    have hder := norm_deriv_weighted_mellinPhase
      ((hw.differentiable (by norm_num)).differentiableAt.hasDerivAt) u ht0
    have hdw : ‖deriv w t‖ ≤ D/t := (le_div_iff₀ ht0).mpr (hwd t ht0)
    calc
      _ ≤ D/t+M*(|u|/t) := hder.trans (add_le_add hdw
        (mul_le_mul_of_nonneg_right (hwm t) (div_nonneg (abs_nonneg _) ht0.le)))
      _ = (D+M*|u|)/t := by ring
      _ ≤ (D+M*|u|)/P := div_le_div_of_nonneg_left
        (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hP htP
  have hint : (∫ t in Ioc a b, ‖deriv (fun t => w t*mellinPhase u t) t‖) ≤
      (R-1)*(D+M*|u|) := by
    rw [←intervalIntegral.integral_of_le hab]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    have hn : 0 ≤ ∫ t in a..b, ‖deriv (fun t => w t*mellinPhase u t) t‖ :=
      intervalIntegral.integral_nonneg_of_forall hab (fun _ => _root_.norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg (sub_nonneg.mpr hab)] at hi
    apply hi.trans
    calc
      (D+M*|u|)/P*(b-a) ≤ (D+M*|u|)/P*((R-1)*P) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (div_nonneg
          (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hP.le)
      _ = (R-1)*(D+M*|u|) := by field_simp
  have hnorm (x : ℝ) : ‖w x*mellinPhase u x‖ ≤ M := by
    simpa only [norm_mul,mellinPhase_norm,mul_one] using hwm x
  linarith [hnorm a,hnorm b]

lemma primeDetectorCutoff_rescaled_smooth (c : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => (primeDetectorCutoff (t/c):ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (primeDetectorCutoff_smooth.comp (contDiff_id.div_const c))

lemma primeDetectorCutoff_rescaled_deriv {D : ℝ}
    (hD : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ D)
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ‖deriv (fun x : ℝ => (primeDetectorCutoff (x/c):ℂ)) t‖*t ≤ D := by
  have hd := (((primeDetectorCutoff_smooth.differentiable (by norm_num)).differentiableAt
    (x := t/c)).hasDerivAt.comp t ((hasDerivAt_id t).div_const c)).ofReal_comp
  change HasDerivAt (fun x : ℝ => (primeDetectorCutoff (x/c):ℂ))
    ((deriv primeDetectorCutoff (t/c)*(1/c):ℝ):ℂ) t at hd
  rw [hd.deriv,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (div_pos zero_lt_one hc)]
  convert hD (t/c) (div_pos ht hc) using 1 <;> first | rfl | ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedPrimeVariation
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radial weights when the largest prime lies in a distinguished
tuple coordinate. The detector difference has a uniform scaled derivative,
so the original smooth weight, rather than an arbitrary bounded sequence,
can be used in prime partial summation. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma detector_difference_smooth (w z : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ =>
      (primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ)) :=
  (primeDetectorCutoff_rescaled_smooth w).sub (primeDetectorCutoff_rescaled_smooth z)

lemma detector_difference_norm (w z x : ℝ) :
    ‖(primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ)‖ ≤ 1 := by
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [primeDetectorCutoff_nonneg (x/w),primeDetectorCutoff_le_one (x/w),
    primeDetectorCutoff_nonneg (x/z),primeDetectorCutoff_le_one (x/z)]

lemma detector_difference_deriv {E : ℝ}
    (hE : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ E)
    {w z x : ℝ} (hw : 0 < w) (hz : 0 < z) (hx : 0 < x) :
    ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)-
      (primeDetectorCutoff (t/z):ℂ)) x‖*x ≤ 2*E := by
  have hdw := ((primeDetectorCutoff_rescaled_smooth w).differentiable
    (by norm_num)).differentiableAt (x := x)
  have hdz := ((primeDetectorCutoff_rescaled_smooth z).differentiable
    (by norm_num)).differentiableAt (x := x)
  have he : deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)-
      (primeDetectorCutoff (t/z):ℂ)) x =
      deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)) x-
        deriv (fun t : ℝ => (primeDetectorCutoff (t/z):ℂ)) x := by
    exact deriv_fun_sub hdw hdz
  rw [he]
  calc
    _ ≤ (‖deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)) x‖+
        ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/z):ℂ)) x‖)*x :=
      mul_le_mul_of_nonneg_right (norm_sub_le _ _) hx.le
    _ = ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)) x‖*x+
        ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/z):ℂ)) x‖*x := by ring
    _ ≤ E+E := add_le_add (primeDetectorCutoff_rescaled_deriv hE hw hx)
      (primeDetectorCutoff_rescaled_deriv hE hz hx)
    _ = _ := by ring

theorem distinguishedRadialWeight_bounds (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    {M D E w z : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (_hE : 0 ≤ E)
    (hw : 0 < w) (hz : 0 < z) (hWnorm : ∀ x, ‖W x‖ ≤ M)
    (hWderiv : ∀ x, 0 < x → ‖deriv W x‖*x ≤ D)
    (hdet : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ E) :
    ContDiff ℝ ∞ (distinguishedRadialWeight W w z) ∧
    (∀ x, ‖distinguishedRadialWeight W w z x‖ ≤ M) ∧
    (∀ x, 0 < x → ‖deriv (distinguishedRadialWeight W w z) x‖*x ≤ D+2*E*M) := by
  let φ := fun x : ℝ => (primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ)
  have hφ := detector_difference_smooth w z
  refine ⟨hW.mul hφ,?_,?_⟩
  · intro x
    change ‖W x*((primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ))‖ ≤ M
    rw [norm_mul]
    exact (mul_le_mul (hWnorm x) (detector_difference_norm w z x)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  · intro x hx
    have hdW := (hW.differentiable (by norm_num)).differentiableAt (x := x)
    have hdφ := (hφ.differentiable (by norm_num)).differentiableAt (x := x)
    change ‖deriv (fun x => W x*φ x) x‖*x ≤ _
    have he : deriv (fun t => W t*φ t) x = deriv W x*φ x+W x*deriv φ x := by
      exact deriv_fun_mul hdW hdφ
    rw [he]
    calc
      _ ≤ (‖deriv W x*φ x‖+‖W x*deriv φ x‖)*x :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) hx.le
      _ = (‖deriv W x‖*x)*‖φ x‖+‖W x‖*(‖deriv φ x‖*x) := by
        rw [norm_mul,norm_mul]
        ring
      _ ≤ D*1+M*(2*E) := add_le_add
        (mul_le_mul (hWderiv x hx) (detector_difference_norm w z x)
          (_root_.norm_nonneg _) hD)
        (mul_le_mul (hWnorm x) (detector_difference_deriv hdet hw hz hx)
          (mul_nonneg (_root_.norm_nonneg _) hx.le) hM)
      _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongDistinguishedPrime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distinguished-coordinate prime sum follows from the
published prime input and the derived smooth detector variation. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_distinguished_prime_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*P/T^D*((M+V)*(1+|u|)) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := angular_long_prime_interval_bound hEF ℓ hℓ hA hD
  obtain ⟨E,hE,hdet⟩ := primeDetectorCutoff_radial_deriv_bound
  refine ⟨2*C*(3+2*E),P₀,by positivity,hP₀,?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV W hW hWn hWd v hv hnc hNv
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le hP)
  obtain ⟨hsmooth,hnorm,hder⟩ := distinguishedRadialWeight_bounds W hW hM hV hE hw hz hWn hWd hdet
  obtain ⟨hdiff,hint,hvar⟩ := radial_mellin_interval_variation hsmooth hP0 (by norm_num)
    ha hab hb hM (by positivity) hnorm hder u
  have hU : 0 ≤ |u| := abs_nonneg u
  have hfac : 1 ≤ 2+2*E+|u| := by linarith
  have hfac' : 2+2*E+|u| ≤ (3+2*E)*(1+|u|) := by
    nlinarith [mul_nonneg (show 0 ≤ 2+2*E by positivity) hU]
  have hvar' : 2*M+(2-1)*((V+2*E*M)+M*|u|) ≤
      (3+2*E)*((M+V)*(1+|u|)) := by
    calc
      _ = (2+2*E+|u|)*M+V := by ring
      _ ≤ (2+2*E+|u|)*M+(2+2*E+|u|)*V :=
        add_le_add le_rfl (le_mul_of_one_le_left hV hfac)
      _ = (2+2*E+|u|)*(M+V) := by ring
      _ ≤ ((3+2*E)*(1+|u|))*(M+V) :=
        mul_le_mul_of_nonneg_right hfac' (add_nonneg hM hV)
      _ = _ := by ring
  calc
    _ ≤ (C*(2*P)/T^D)*(2*M+(2-1)*((V+2*E*M)+M*|u|)) :=
      (hbound T P 2 a b hT hP hTP ha hab hb v hv hnc hNv _ hdiff hint).trans
        (mul_le_mul_of_nonneg_left hvar (by positivity))
    _ ≤ (C*(2*P)/T^D)*((3+2*E)*((M+V)*(1+|u|))) :=
      mul_le_mul_of_nonneg_left hvar' (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimePowers
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial losses in log X are negligible on the actual long-prime
scale exp(sqrt(log X)). This includes logarithmic prime exclusions. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem long_prime_power_absorption {C D E : ℝ} (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∀ᶠ P : ℝ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ (Real.log P)^2 →
      C*T^E ≤ P/T^D := by
  have hs := ((isLittleO_log_rpow_rpow_atTop (2*(D+E))
    (by norm_num : (0:ℝ) < 1)).const_mul_left C).def zero_lt_one
  filter_upwards [hs,eventually_gt_atTop (1:ℝ)] with P hsmall hP T hT hTP
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hl : 0 < Real.log P := Real.log_pos hP
  have hbound : C*(Real.log P)^(2*(D+E)) ≤ P := by
    simpa only [Real.rpow_one,one_mul,Real.norm_of_nonneg (mul_nonneg hC
      (Real.rpow_nonneg hl.le _)),Real.norm_of_nonneg hP0.le] using hsmall
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hT0 D)).mpr
  calc
    C*T^E*T^D = C*T^(D+E) := by rw [Real.rpow_add hT0]; ring
    _ ≤ C*((Real.log P)^2)^(D+E) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hT0.le hTP (add_nonneg hD hE)) hC
    _ = C*(Real.log P)^(2*(D+E)) := by
      rw [←Real.rpow_natCast_mul hl.le 2 (D+E)]
      norm_num
    _ ≤ P := hbound

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeJoin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma norm_le_of_dvd_nonzero {a b : Eisenstein} (hb : b ≠ 0) (h : a ∣ b) : norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := by intro h; apply hb; rw [h,mul_zero]
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_norm hc)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveMobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primaryPrimeFactors_finset_prod (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) :
    primaryPrimeFactors (∏ p ∈ U, p) = U := by
  have hprod := primary_finset_prod U (fun p : Eisenstein => p) (fun p hp => (hU p hp).1)
  ext p
  rw [primaryPrime_mem_factors_iff hprod]
  constructor
  · rintro ⟨hp,hd⟩
    obtain ⟨q,hq,hpq⟩ := (hp.2.dvd_finsetProd_iff (fun p : Eisenstein => p)).mp hd
    have he : p = q := primary_associated_eq hp.1 (hU q hq).1
      (hp.2.associated_of_dvd (hU q hq).2 hpq)
    exact he ▸ hq
  · intro hp
    exact ⟨hU p hp,Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primary factor tuples in the distinguished-prime expansion.
Ordering a subset contributes its factorial; the remaining primary factor
is the literal complementary product, not an abstract coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedPrimeWeight_support {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 0 < w) (hwz : w ≤ z) {p : Eisenstein}
    (hp : 0 < norm p) (hne : distinguishedPrimeWeight ψ w z p ≠ 0) :
    w < norm p ∧ norm p < 2*z := by
  have hz : 0 < z := hw.trans_le hwz
  constructor
  · by_contra h
    have hpw : norm p ≤ w := not_lt.mp h
    apply hne
    rw [distinguishedPrimeWeight,hψone _ (div_pos hp hw) ((div_le_one hw).mpr hpw),
      hψone _ (div_pos hp hz) ((div_le_one hz).mpr (hpw.trans hwz)),sub_self]
    rfl
  · by_contra h
    have hpz : 2*z ≤ norm p := not_lt.mp h
    apply hne
    rw [distinguishedPrimeWeight,hψzero _ ((le_div_iff₀ hw).mpr (by linarith)),
      hψzero _ ((le_div_iff₀ hz).mpr hpz),sub_self]
    rfl

/-- Every chosen prime is large; the product bound therefore bounds the
number of chosen factors, uniformly in the original squarefree element. -/
lemma primary_factor_subset_card_lt {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n)
    {w : ℝ} (hw : 1 ≤ w) (hlarge : ∀ p ∈ s, w ≤ norm p)
    {k : ℕ} (hsize : norm n < w^k) : s.card < k := by
  have hprod : w^s.card ≤ norm n := by
    calc
      _ = ∏ _p ∈ s, w := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ s, norm p := Finset.prod_le_prod (fun _ _ => zero_le_one.trans hw) hlarge
      _ ≤ (∏ p ∈ s, norm p)*(∏ p ∈ primaryPrimeFactors n \ s, norm p) :=
        le_mul_of_one_le_right (Finset.prod_nonneg (fun p _ => norm_nonneg p))
          (Finset.one_le_prod (fun p hp => one_le_norm
            (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp hp).1).1.2.ne_zero))
      _ = ∏ p ∈ primaryPrimeFactors n, norm p := by
        rw [mul_comm,Finset.prod_sdiff hsub]
      _ = norm n := by
        simpa only [Nat.cast_prod,normNat_cast] using
          congrArg (fun m : ℕ => (m:ℝ)) (primaryPrimeFactors_norm_prod hn hs)
  by_contra h
  exact (not_lt_of_ge ((pow_le_pow_right₀ hw (not_lt.mp h)).trans hprod)) hsize

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBinGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform norm distortion for the multiplicative bin surrogate.
The bin ratio is fixed before the norm parameter; all selected subsets
simultaneously satisfy the manuscript's small-power distortion bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_norm_ge_two {p : Eisenstein} (hp : primaryPrime p) : 2 ≤ norm p := by
  have hz := normNat_ne_zero hp.2.ne_zero
  have ho : normNat p ≠ 1 := by
    intro h
    apply hp.2.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [←normNat_cast,h]
    norm_num
  have h : 2 ≤ normNat p := by omega
  rw [←normNat_cast]
  exact_mod_cast h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit cost of the coprimality exclusion in a prime constituent.
It follows from the proved ideal-divisor bound, uniformly in the excluded
element, and will be subtracted from the prime Siegel–Walfisz estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_exclusion_difference (S : Finset Eisenstein) (e : Eisenstein)
    (w : Eisenstein → ℂ) {M : ℝ} (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p)‖ ≤
      M*((S.filter (fun p => ¬ IsCoprime p e)).card:ℝ) := by
  have he : (∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p) =
      ∑ p ∈ S with ¬ IsCoprime p e, w p := by
    rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : IsCoprime p e <;> simp only [hp,ite_true, if_true,ite_false, if_false,not_true_eq_false,
      not_false_eq_true,sub_self,sub_zero]
  rw [he]
  calc
    _ ≤ ∑ p ∈ S with ¬ IsCoprime p e, ‖w p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ S with ¬ IsCoprime _p e, M :=
      Finset.sum_le_sum (fun p hp => hw p (Finset.mem_filter.mp hp).1)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusionLog
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic, rather than merely subpower, number of prime
exclusions. This is necessary when the free prime is exp(sqrt(log X)). -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primary_prime_divisor_card_log (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (e : Eisenstein) (he : e ≠ 0) :
    ((S.filter (fun p => p ∣ e)).card:ℝ) ≤ Real.log (norm e)/Real.log 2 := by
  let T := S.filter (fun p => p ∣ e)
  have hp (p : Eisenstein) (hp : p ∈ T) : primaryPrime p :=
    hS p (Finset.mem_filter.mp hp).1
  have hd : (∏ p ∈ T, p) ∣ e := by
    apply Finset.prod_dvd_of_coprime
    · intro p hpT q hqT hpq
      exact primaryPrimes_isCoprime (hp p hpT) (hp q hqT) hpq
    · intro p hpT
      exact (Finset.mem_filter.mp hpT).2
  have hprod : (2:ℝ)^T.card ≤ norm e := by
    calc
      _ = ∏ _p ∈ T, (2:ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ T, norm p := Finset.prod_le_prod (fun _ _ => by norm_num)
        (fun p hpT => primaryPrime_norm_ge_two (hp p hpT))
      _ = norm (∏ p ∈ T, p) := (norm_finset_prod _ _).symm
      _ ≤ norm e := norm_le_of_dvd_nonzero he hd
  have hn : 0 < norm e := zero_lt_one.trans_le (one_le_norm he)
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr
  exact (Real.pow_le_iff_le_log (by norm_num : (0:ℝ) < 2) hn).mp hprod

theorem prime_exclusion_logarithmic (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (e : Eisenstein) (he : e ≠ 0)
    (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p)‖ ≤
      M*(Real.log (norm e)/Real.log 2) := by
  have hsub : S.filter (fun p => ¬IsCoprime p e) ⊆ S.filter (fun p => p ∣ e) := by
    intro p hp
    obtain ⟨hpS,hp⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpS,?_⟩
    by_contra hn
    exact hp ((hS p hpS).2.irreducible.coprime_iff_not_dvd.mpr hn)
  exact (prime_exclusion_difference S e w hw).trans
    (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (primary_prime_divisor_card_log S hS e he)) hM)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongDistinguishedSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exclusion and arbitrary logarithmic saving for the actual smooth
weight of a distinguished free prime. The bounds retain the derivative
cost and are uniform in the two detector scales. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_distinguished_prime_excluded_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ T^A → e ≠ 0 →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p e),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*P/T^D*((M+V)*(1+|u|))+M*(Real.log (norm e)/Real.log 2) := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_distinguished_prime_bound hEF ℓ hℓ hA hD
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV W hW hWn hWd v e hv hnc hNv he
  let S := (primeCutoff b).filter (fun p => a < norm p)
  let f := fun p : Eisenstein =>
    distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ M := by
    dsimp [f,distinguishedRadialWeight]
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,mul_one]
    have hfirst : ‖W (norm p)‖*
        ‖(primeDetectorCutoff (norm p/w):ℂ)-(primeDetectorCutoff (norm p/z):ℂ)‖ ≤ M := by
      exact (mul_le_mul (hWn _) (detector_difference_norm w z (norm p))
        (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
    exact (mul_le_mul hfirst (angularCubicSymbol_norm_le_one ℓ (hS p hp).1 v)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  have hex := prime_exclusion_logarithmic S hS e he f hM hf
  change ‖∑ p ∈ S with IsCoprime p e, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S, f p‖+
        ‖(∑ p ∈ S, f p)-(∑ p ∈ S with IsCoprime p e, f p)‖ :=
      norm_le_norm_add_norm_sub _ _
    _ ≤ K*P/T^D*((M+V)*(1+|u|))+M*(Real.log (norm e)/Real.log 2) :=
      add_le_add (hbound T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV W
        hW hWn hWd v hv hnc hNv) hex

theorem angular_long_distinguished_prime_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ T^A → e ≠ 0 → Real.log (norm e) ≤ T^E →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p e),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_distinguished_prime_excluded_bound hEF ℓ hℓ hA
    (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hD hF) hH)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := (Real.log 2)⁻¹) (D := D) (E := F+E)
      (inv_nonneg.mpr hlog2.le) hD.le (add_nonneg hF hE))
  refine ⟨2*K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV hu hMV W hW hWn hWd
    v e hv hnc hNv he hNe
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  have hheight : 1+|u| ≤ 2*T^H := by
    linarith [Real.one_le_rpow hT hH]
  have hMbound : M ≤ T^F := (le_add_of_nonneg_right hV).trans hMV
  have hmain : K*P/T^(D+F+H)*((M+V)*(1+|u|)) ≤ 2*K*P/T^D := by
    calc
      _ ≤ K*P/T^(D+F+H)*(T^F*(2*T^H)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hMV hheight
          (by positivity) (Real.rpow_nonneg hT0.le _)) (by positivity)
      _ = _ := by
        rw [Real.rpow_add hT0,Real.rpow_add hT0]
        field_simp
  have herror : M*(Real.log (norm e)/Real.log 2) ≤ P/T^D := by
    calc
      _ ≤ T^F*(T^E/Real.log 2) := mul_le_mul hMbound
        ((div_le_div_iff_of_pos_right hlog2).mpr hNe)
        (div_nonneg (Real.log_nonneg (one_le_norm he)) hlog2.le)
        (Real.rpow_nonneg hT0.le _)
      _ = (Real.log 2)⁻¹*T^(F+E) := by rw [Real.rpow_add hT0]; ring
      _ ≤ _ := hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  apply (hbound T P a b w z u M V hT ((le_max_left _ _).trans hP) hTP ha hab hb
    hw hz hM hV W hW hWn hWd v e hv hnc hNv he).trans
  calc
    _ ≤ 2*K*P/T^D+P/T^D := add_le_add hmain herror
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIntervalGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The stopped crossing tests with one prime left free. A distinguished
prime enters by its actual norm; a selected-bin prime leaves every
surrogate prefix unchanged while its bin is fixed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- A fixed-order tie rule changes the lower norm interval at just the
single norm of the largest complementary prime. -/
lemma largestPrimePredicate_away_tie (code : Eisenstein → ℕ)
    (s : Finset Eisenstein) (p : Eisenstein) (hne : normNat p ≠ s.sup normNat) :
    largestPrimePredicate code s p ↔ s.sup normNat < normNat p := by
  constructor
  · intro h
    have hs : s.sup normNat ≤ normNat p := by
      apply Finset.sup_le
      intro q hq
      rcases h q hq with hlt | he
      · exact hlt.le
      · exact he.1.le
    exact lt_of_le_of_ne hs hne.symm
  · intro h q hq
    exact Or.inl ((Finset.le_sup (f := normNat) hq).trans_lt h)

lemma crossing_norm_interval {a S ell Z x : ℝ} (ha : 0 < a)
    (hS : 0 < S) (hell : 0 < ell) :
    (a*x*S/ell < Z ∧ Z ≤ a*x*S) ↔
      Z/(a*S) ≤ x ∧ x < Z*ell/(a*S) := by
  have hAS : 0 < a*S := mul_pos ha hS
  have he : a*x*S = x*(a*S) := by ring
  rw [he]
  constructor
  · rintro ⟨hu,hl⟩
    exact ⟨(div_le_iff₀ hAS).mpr (by nlinarith),
      (lt_div_iff₀ hAS).mpr ((div_lt_iff₀ hell).mp hu)⟩
  · rintro ⟨hl,hu⟩
    exact ⟨(div_lt_iff₀ hell).mpr ((lt_div_iff₀ hAS).mp hu),
      (div_le_iff₀ hAS).mp hl⟩

lemma distinguished_prime_crossing_interval {r p : Eisenstein}
    (hr : r ≠ 0) {S ell Z : ℝ} (hS : 0 < S) (hell : 0 < ell) :
    (norm (r*p)*S/ell < Z ∧ Z ≤ norm (r*p)*S) ↔
      Z/(norm r*S) ≤ norm p ∧ norm p < Z*ell/(norm r*S) := by
  rw [norm_mul_eq]
  exact crossing_norm_interval (norm_pos_of_ne_zero hr) hS hell

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeSelection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact selection of a largest prime, with a fixed injective tie code.
This is an unordered selection: inserting it into a finite sum introduces
no factor depending on the number of primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeTieCode_injective : Function.Injective primeTieCode := by
  intro p q h
  have hi : Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p =
      Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q := Encodable.encode_injective h
  have hr := Function.rightInverse_invFun ofCoords_surjective
  calc
    p = ofCoords (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p).1
      (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p).2 := (hr p).symm
    _ = ofCoords (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q).1
      (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q).2 := by rw [hi]
    _ = q := hr q

lemma largestPrime_unique {code : Eisenstein → ℕ} (hc : Function.Injective code)
    {s : Finset Eisenstein} {p q : Eisenstein} (hp : p ∈ s) (hq : q ∈ s)
    (hpl : largestPrimePredicate code s p) (hql : largestPrimePredicate code s q) : p = q := by
  rcases hpl q hq with hlt | he
  · rcases hql p hp with hlt' | he'
    · omega
    · omega
  · rcases hql p hp with hlt' | he'
    · omega
    · exact hc (le_antisymm he'.2 he.2)

lemma selectedLargestPrime_spec (s : Finset Eisenstein) (hs : s.Nonempty) :
    selectedLargestPrime s hs ∈ s ∧
      largestPrimePredicate primeTieCode s (selectedLargestPrime s hs) :=
  Classical.choose_spec (exists_largestPrime primeTieCode s hs)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal independent coefficients from the stopping construction.
The selected-side test may contain the first-stage failure and crossing
conditions; the remaining-side test is a separate condition on its divisor.
No coprimality condition is inserted between the two sides. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPairCoefficient_sum (S T : Finset Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) (F : Eisenstein → ℂ) :
    (∑ b ∈ primaryPairSupport S T, primaryPairCoefficient S T w b*F b) =
      ∑ p ∈ S ×ˢ T, w p*F (p.1*p.2) := by
  unfold primaryPairCoefficient primaryPairFiber
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ b ∈ primaryPairSupport S T,
        ∑ p ∈ S ×ˢ T with p.1*p.2 = b, w p*F (p.1*p.2) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image_of_mem _ hp) _

lemma primaryPairFiber_card_le (S T : Finset Eisenstein)
    (hS : ∀ r ∈ S, primary r) (b : Eisenstein) :
    (primaryPairFiber S T b).card ≤ (S.filter (fun r => r ∣ b)).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨hm.1,⟨p.2,(Finset.mem_filter.mp hp).2.symm⟩⟩
  · intro p hp q hq he
    apply Prod.ext he
    have hmul : p.1*p.2 = p.1*q.2 := by
      calc
        _ = b := (Finset.mem_filter.mp hp).2
        _ = q.1*q.2 := (Finset.mem_filter.mp hq).2.symm
        _ = _ := by rw [he]
    exact mul_left_cancel₀ (primary_ne_zero
      (hS p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)) hmul

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficientBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise bounds for the actual stopped coefficients, before any
analytic sequence estimate. The divisor count is literal and introduces
no dependence on the number or width of prime bins. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_norm_le_one {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ) (d : Eisenstein) :
    ‖cutoffMoebius ψ w d‖ ≤ 1 := by
  rw [cutoffMoebius,norm_mul,norm_prod]
  have hp : (∏ p ∈ primaryPrimeFactors d, ‖(ψ (norm p/w):ℂ)‖) ≤ 1 := by
    apply Finset.prod_le_one (fun _ _ => _root_.norm_nonneg _)
    intro p hp
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hψ _).1] using (hψ (norm p/w)).2
  exact (mul_le_mul (norm_idealMoebius_le_one d) hp
    (Finset.prod_nonneg (fun _ _ => _root_.norm_nonneg _)) zero_le_one).trans_eq (one_mul 1)

lemma primeDetectorCutoff_moebius_norm (w : ℝ) (d : Eisenstein) :
    ‖cutoffMoebius primeDetectorCutoff w d‖ ≤ 1 :=
  cutoffMoebius_norm_le_one (fun x => ⟨primeDetectorCutoff_nonneg x,
    primeDetectorCutoff_le_one x⟩) w d

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeNormEndpoints
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint and largest-prime tie corrections. At most two primary
primes have a prescribed norm, so endpoint choices cost an absolute
constant in a bounded prime sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_eq_or_conjugate_of_norm_eq {p q : Eisenstein}
    (hp : primaryPrime p) (hq : primaryPrime q) (hn : norm p = norm q) :
    p = q ∨ p = conjugate q := by
  have hnr : (normNat p:ℝ) = normNat q := by simpa only [normNat_cast] using hn
  have hn' : normNat p = normNat q := by exact_mod_cast hnr
  have heq : p*conjugate p = q*conjugate q := by
    rw [←normNat_cast_eq_mul_conjugate,←normNat_cast_eq_mul_conjugate,hn']
  have hd : p ∣ q*conjugate q := heq ▸ dvd_mul_right p (conjugate p)
  rcases hp.2.dvd_or_dvd hd with hd | hd
  · exact Or.inl (primary_associated_eq hp.1 hq.1
      ((hp.2.dvd_prime_iff_associated hq.2).mp hd))
  · exact Or.inr (primary_associated_eq hp.1 (primaryPrime_conjugate hq).1
      ((hp.2.dvd_prime_iff_associated (primaryPrime_conjugate hq).2).mp hd))

theorem primaryPrime_norm_fiber_card (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (x : ℝ) :
    (S.filter (fun p => norm p = x)).card ≤ 2 := by
  let T := S.filter (fun p => norm p = x)
  by_cases hT : T.Nonempty
  · obtain ⟨q,hq⟩ := hT
    have hsub : T ⊆ {q,conjugate q} := by
      intro p hp
      have he := primaryPrime_eq_or_conjugate_of_norm_eq
        (hS p (Finset.mem_filter.mp hp).1) (hS q (Finset.mem_filter.mp hq).1)
        ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
      simpa only [Finset.mem_insert,Finset.mem_singleton] using he
    apply (Finset.card_le_card hsub).trans
    calc
      ({q,conjugate q}:Finset Eisenstein).card ≤ ({conjugate q}:Finset Eisenstein).card+1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  · change T.card ≤ 2
    rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    norm_num

lemma primaryPrime_two_norm_card (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a b : ℝ) :
    (S.filter (fun p => norm p = a ∨ norm p = b)).card ≤ 4 := by
  have he : S.filter (fun p => norm p = a ∨ norm p = b) =
      S.filter (fun p => norm p = a) ∪ S.filter (fun p => norm p = b) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_union]
    tauto
  rw [he]
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add (primaryPrime_norm_fiber_card S hS a)
      (primaryPrime_norm_fiber_card S hS b)).trans (by norm_num))

/-- This also covers an arbitrary fixed-order selection among equal-norm
largest primes. Away from the two boundary norms the predicates agree. -/
theorem prime_interval_endpoint_difference (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (P Q : Eisenstein → Prop) (a b : ℝ)
    (hPQ : ∀ p ∈ S, norm p ≠ a → norm p ≠ b → (P p ↔ Q p))
    (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S with P p, w p)-(∑ p ∈ S with Q p, w p)‖ ≤ 4*M := by
  let T := S.filter (fun p => norm p = a ∨ norm p = b)
  let f := fun p => (if P p then w p else 0)-(if Q p then w p else 0)
  have he : (∑ p ∈ S, f p) = ∑ p ∈ T, f p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hn : norm p ≠ a ∧ norm p ≠ b := by
      simpa only [T,Finset.mem_filter,hp,true_and,not_or] using hnot
    have he := hPQ p hp hn.1 hn.2
    by_cases h : P p
    · simp [f,h,he.mp h]
    · have hq : ¬Q p := fun hq => h (he.mpr hq)
      simp [f,h,hq]
  have hf (p : Eisenstein) (hp : p ∈ T) : ‖f p‖ ≤ M := by
    have hpS := (Finset.mem_filter.mp hp).1
    by_cases hP : P p <;> by_cases hQ : Q p <;>
      simp [f,hP,hQ,hM,hw p hpS]
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_sub_distrib]
  change ‖∑ p ∈ S, f p‖ ≤ _
  rw [he]
  calc
    _ ≤ ∑ p ∈ T, ‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, M := Finset.sum_le_sum hf
    _ = (T.card:ℝ)*M := by simp
    _ ≤ 4*M := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (primaryPrime_two_norm_card S hS a b)) hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeCancellation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual largest-prime restriction costs only the two equal-norm
endpoints. The cancellation is still the published prime input, not a
sequence-condition hypothesis. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrime_endpoint_difference (code : Eisenstein → ℕ)
    (C S : Finset Eisenstein) (hS : ∀ p ∈ S, primaryPrime p)
    (f : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ p ∈ S, ‖f p‖ ≤ M) :
    ‖(∑ p ∈ S with largestPrimePredicate code C p, f p)-
      (∑ p ∈ S with ((C.sup normNat:ℕ):ℝ) < norm p, f p)‖ ≤ 4*M := by
  apply prime_interval_endpoint_difference S hS _ _
    ((C.sup normNat:ℕ):ℝ) ((C.sup normNat:ℕ):ℝ) _ f hM hf
  intro p hp hn _
  have hne : normNat p ≠ C.sup normNat := by
    intro h
    apply hn
    rw [←normNat_cast p,h]
  simpa only [←normNat_cast p,Nat.cast_lt] using
    largestPrimePredicate_away_tie code C p hne

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongDistinguishedContext
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A distinguished free prime is cancelled with the actual largest-prime
tie rule relative to the entire fixed complement. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_distinguished_context_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ (v e : Eisenstein) (C : Finset Eisenstein), v ≠ 0 →
      (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
      Real.log (norm e) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p e)).filter (fun p => largestPrimePredicate primeTieCode C p),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_distinguished_prime_saving hEF ℓ hℓ hA hD hH hE hF
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := F)
      (by norm_num) hD.le hF)
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV hu hMV W hW hWn hWd
    v e C hv hnc hNv he hNe
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := ((primeCutoff b).filter (fun p => a < norm p)).filter (fun p => IsCoprime p e)
  let f := fun p : Eisenstein =>
    distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v
  let m : ℝ := ((C.sup normNat:ℕ):ℝ)
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ M := by
    dsimp [f,distinguishedRadialWeight]
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,mul_one]
    have hfirst : ‖W (norm p)‖*
        ‖(primeDetectorCutoff (norm p/w):ℂ)-(primeDetectorCutoff (norm p/z):ℂ)‖ ≤ M :=
      (mul_le_mul (hWn _) (detector_difference_norm w z (norm p))
        (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
    exact (mul_le_mul hfirst (angularCubicSymbol_norm_le_one ℓ (hS p hp).1 v)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  have hend := largestPrime_endpoint_difference primeTieCode C S hS f hM hf
  have hinterval : (∑ p ∈ S with m < norm p, f p) =
      ∑ p ∈ ((primeCutoff b).filter (fun p => max a m < norm p)).filter
        (fun p => IsCoprime p e), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,max_lt_iff]
    tauto
  have hsum : ‖∑ p ∈ S with m < norm p, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hm : max a m ≤ b
    · exact hbound T P (max a m) b w z u M V hT ((le_max_left _ _).trans hP) hTP
        (ha.trans (le_max_left _ _)) hm hb hw hz hM hV hu hMV W hW hWn hWd
        v e hv hnc hNv he hNe
    · have hempty : ((primeCutoff b).filter (fun p => max a m < norm p)).filter
          (fun p => IsCoprime p e) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp,_⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hp
        exact hm (hl.le.trans (mem_primeCutoff.mp hp).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have hfour : 4*M ≤ P/T^D :=
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hV).trans hMV) (by norm_num)).trans
      (hP₁ P ((le_max_right _ _).trans hP) T hT hTP)
  change ‖∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with m < norm p, f p‖+
        ‖(∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p)-
          (∑ p ∈ S with m < norm p, f p)‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4*M := add_le_add hsum hend
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl hfour
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMixedInterval
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intersections of the half-open norm restrictions arising from the
crossing test differ from the prime interval convention only at their
two final endpoints. -/
noncomputable section
namespace CubicFirstMoment

lemma mixed_norm_interval_away {a l b h x : ℝ}
    (hlo : x ≠ max a l) (hhi : x ≠ min b h) :
    (a < x ∧ l ≤ x ∧ x < b ∧ x ≤ h) ↔ max a l < x ∧ x ≤ min b h := by
  constructor
  · rintro ⟨ha,hl,hb,hh⟩
    refine ⟨?_,le_min hb.le hh⟩
    have hmx : max a l ≤ x := max_le ha.le hl
    exact lt_of_le_of_ne hmx hlo.symm
  · rintro ⟨hl,hh⟩
    have ha : a < x := (le_max_left _ _).trans_lt hl
    have hle : l ≤ x := ((le_max_right _ _).trans_lt hl).le
    have hb : x ≤ b := hh.trans (min_le_left _ _)
    have hstrict : x < b := by
      by_contra hn
      have hxb : x = b := le_antisymm hb (le_of_not_gt hn)
      have hxh : x ≤ h := hh.trans (min_le_right _ _)
      have hmin : min b h = x := by rw [←hxb,min_eq_left hxh]
      exact hhi hmin.symm
    exact ⟨ha,hle,hstrict,hh.trans (min_le_right _ _)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongDistinguishedInterval
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The half-open intersections supplied by the actual stopping tests
inherit prime cancellation. Only the two final endpoint norms are lost. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_distinguished_mixed_interval_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P B a l b h w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ max a l → min b h ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ (v e : Eisenstein) (C : Finset Eisenstein), v ≠ 0 →
      (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      Real.log (norm e) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff B).filter (fun p => IsCoprime p e)).filter
          (fun p => largestPrimePredicate primeTieCode C p)).filter
          (fun p => a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_distinguished_context_saving hEF ℓ hℓ hA hD hH hE hF
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := F)
      (by norm_num) hD.le hF)
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P B a l b h w z u M V hT hP hTP hlow hupp hw hz hM hV hheight hMV W hW hWn hWd
    v e C hv hnc hNv he hNe
  have hPpos : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := ((primeCutoff B).filter (fun p => IsCoprime p e)).filter
    (fun p => largestPrimePredicate primeTieCode C p)
  let f := fun p : Eisenstein =>
    distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ M := by
    dsimp [f,distinguishedRadialWeight]
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,mul_one]
    have hfirst : ‖W (norm p)‖*
        ‖(primeDetectorCutoff (norm p/w):ℂ)-(primeDetectorCutoff (norm p/z):ℂ)‖ ≤ M :=
      (mul_le_mul (hWn _) (detector_difference_norm w z (norm p))
        (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
    exact (mul_le_mul hfirst (angularCubicSymbol_norm_le_one ℓ (hS p hp).1 v)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  have hend := prime_interval_endpoint_difference S hS
    (fun p => a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h)
    (fun p => max a l < norm p ∧ norm p ≤ min b h) (max a l) (min b h)
    (fun p _ hlo hhi => mixed_norm_interval_away hlo hhi) f hM hf
  have hinterval : (∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p) =
      ∑ p ∈ (((primeCutoff (min B (min b h))).filter (fun p => max a l < norm p)).filter
        (fun p => IsCoprime p e)).filter
        (fun p => largestPrimePredicate primeTieCode C p), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,mem_primeCutoff,le_min_iff]
    tauto
  have hmain : ‖∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hab : max a l ≤ min B (min b h)
    · exact hbound T P (max a l) (min B (min b h)) w z u M V hT
        ((le_max_left _ _).trans hP) hTP hlow hab ((min_le_right _ _).trans hupp)
        hw hz hM hV hheight hMV W hW hWn hWd v e C hv hnc hNv he hNe
    · have hempty : (((primeCutoff (min B (min b h))).filter (fun p => max a l < norm p)).filter
          (fun p => IsCoprime p e)).filter (fun p => largestPrimePredicate primeTieCode C p) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have hm := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        exact hab (hm.2.le.trans (mem_primeCutoff.mp hm.1).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have herr : 4*M ≤ P/T^D :=
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hV).trans hMV) (by norm_num)).trans
      (hP₁ P ((le_max_right _ _).trans hP) T hT hTP)
  change ‖∑ p ∈ S with a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p‖+
        ‖(∑ p ∈ S with a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h, f p)-
          (∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p)‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4*M := add_le_add hmain (by
      convert hend using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      all_goals
        apply Finset.sum_congr
        · ext p
          simp only [Finset.mem_filter]
        · intro p hp
          rfl)
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl herr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimeIntervals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete selected-side stopping predicates. Replacing one prime
within its fixed bin leaves every selected-bin surrogate test unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_prime_mul {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c) :
    primaryPrimeFactors (p*c) = insert p (primaryPrimeFactors c) := by
  have hpnot : p ∉ primaryPrimeFactors c :=
    fun h => hpc (primaryPrimeFactor_spec hc h).2
  have hprime : ∀ q ∈ insert p (primaryPrimeFactors c), primaryPrime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (primaryPrimeFactor_spec hc hq).1
  have h := primaryPrimeFactors_finset_prod (insert p (primaryPrimeFactors c)) hprime
  simpa only [Finset.prod_insert hpnot,primaryPrimeFactors_prod hc hs] using h

/-- If the free prime is distinguished, the actual stopping inequalities
are a single norm interval; the selected divisor remains fixed. -/
theorem stoppingSideTest_free_distinguished_interval
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ)
    {c : Eisenstein} (hc : c ≠ 0) (d p : Eisenstein)
    (hell : 0 < ell j)
    (hS : 0 < primeSurrogate (primaryPrimeFactors d) bin ell) :
    stoppingSideTest bin ell j k Z (c*p) d ↔
      (∀ q ∈ primaryPrimeFactors d, bin q ≤ j) ∧
      (primeBin (primaryPrimeFactors d) bin j).card = k ∧
      Z/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell) ≤ norm p ∧
      norm p < Z*ell j/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell) := by
  unfold stoppingSideTest stoppingPrimeSetTest
  rw [distinguished_prime_crossing_interval hc hS hell]

lemma failedStage_free_distinguished_interval {c p : Eisenstein} (hc : c ≠ 0)
    {S Q : ℝ} (hS : 0 < S) :
    norm (c*p)*S < Q ↔ norm p < Q/(norm c*S) := by
  rw [norm_mul_eq,lt_div_iff₀ (mul_pos (norm_pos_of_ne_zero hc) hS)]
  ring_nf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimePredicate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both actual stopping branches, including failure of the earlier
crossing test. Fixing the selected prime's bin fixes all these tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stoppedSideTest_free_distinguished_interval
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ) (Z Q : ℝ) (early : Bool)
    {c : Eisenstein} (hc : c ≠ 0) (d p : Eisenstein) (hell : 0 < ell j)
    (hS : 0 < primeSurrogate (primaryPrimeFactors d) bin ell)
    (hE : 0 < primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell) :
    stoppedSideTest bin ell j k h Z Q early (c*p) d ↔
      ((∀ q ∈ primaryPrimeFactors d, bin q ≤ j) ∧
      (primeBin (primaryPrimeFactors d) bin j).card = k ∧
      Z/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell) ≤ norm p ∧
      norm p < Z*ell j/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell)) ∧
      (early = true ∨ norm p < Q/(norm c*
        primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell)) := by
  unfold stoppedSideTest
  rw [stoppingSideTest_free_distinguished_interval bin ell j k Z hc d p hell hS,
    failedStage_free_distinguished_interval hc hE]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeBins
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete descending geometric binning of the actual prime norms.
The number of bins is logarithmic and all lower endpoints exceed one,
so the exact first-crossing construction applies without empty-bin cases. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma geometricBinLower_gt_one {ρ B : ℝ} (hρ : 1 < ρ)
    {j : ℕ} (hj : j < geometricBinCount ρ B) : 1 < geometricBinLower ρ B j := by
  exact one_lt_pow₀ hρ (by omega)

lemma geometricPrimeBin_cell {ρ B : ℝ} (hρ : 1 < ρ) (_hρ₂ : ρ ≤ 2)
    {p : Eisenstein} (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricBinLower ρ B (geometricPrimeBin ρ B p) ≤ norm p ∧
      norm p < ρ*geometricBinLower ρ B (geometricPrimeBin ρ B p) := by
  have hr := Real.log_pos hρ
  have hpn : 0 < norm p := by linarith [primaryPrime_norm_ge_two hp]
  have hl : 0 ≤ Real.log (norm p)/Real.log ρ :=
    div_nonneg (Real.log_nonneg (by linarith [primaryPrime_norm_ge_two hp])) hr.le
  have hkM : ⌊Real.log (norm p)/Real.log ρ⌋₊ ≤ geometricBinCount ρ B := by
    exact (Nat.floor_mono (div_le_div_of_nonneg_right
      (Real.log_le_log hpn hpB) hr.le)).trans (Nat.floor_le_ceil _)
  have hidx : geometricBinCount ρ B - geometricPrimeBin ρ B p =
      ⌊Real.log (norm p)/Real.log ρ⌋₊ := by
    unfold geometricPrimeBin
    omega
  change ρ^(geometricBinCount ρ B-geometricPrimeBin ρ B p) ≤ norm p ∧
    norm p < ρ*ρ^(geometricBinCount ρ B-geometricPrimeBin ρ B p)
  rw [hidx]
  constructor
  · apply (Real.pow_le_iff_le_log (zero_lt_one.trans hρ) hpn).mpr
    exact (le_div_iff₀ hr).mp (Nat.floor_le hl)
  · rw [←pow_succ',Real.lt_pow_iff_log_lt hpn (zero_lt_one.trans hρ)]
    have h := (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (Real.log (norm p)/Real.log ρ))
    simpa only [Nat.cast_add,Nat.cast_one] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeIntervals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact norm intervals for the concrete bins used by the stopping
construction, including their bounded endpoint convention change. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem geometricPrimeBin_eq_iff {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) {p : Eisenstein}
    (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricPrimeBin ρ B p = j ↔
      geometricBinLower ρ B j ≤ norm p ∧ norm p < ρ*geometricBinLower ρ B j := by
  constructor
  · intro he
    simpa only [he] using geometricPrimeBin_cell hρ hρ₂ hp hpB
  · intro hcell
    have hr : 0 < Real.log ρ := Real.log_pos hρ
    have hpn : 0 < norm p := by linarith [primaryPrime_norm_ge_two hp]
    have hn : 0 ≤ Real.log (norm p)/Real.log ρ :=
      div_nonneg (Real.log_nonneg (by linarith [primaryPrime_norm_ge_two hp])) hr.le
    have hlo : ((geometricBinCount ρ B-j:ℕ):ℝ) ≤ Real.log (norm p)/Real.log ρ := by
      apply (le_div_iff₀ hr).mpr
      exact (Real.pow_le_iff_le_log (zero_lt_one.trans hρ) hpn).mp hcell.1
    have hhi : Real.log (norm p)/Real.log ρ < ((geometricBinCount ρ B-j:ℕ):ℝ)+1 := by
      apply (div_lt_iff₀ hr).mpr
      have h : norm p < ρ^(geometricBinCount ρ B-j+1) := by
        simpa only [pow_succ',geometricBinLower] using hcell.2
      simpa only [Nat.cast_add,Nat.cast_one] using
        (Real.lt_pow_iff_log_lt hpn (zero_lt_one.trans hρ)).mp h
    have hf : ⌊Real.log (norm p)/Real.log ρ⌋₊ = geometricBinCount ρ B-j :=
      (Nat.floor_eq_iff hn).mpr ⟨hlo,hhi⟩
    unfold geometricPrimeBin
    rw [hf]
    omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeCanonical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical functions for the exact largest-prime change of variables.
They allow predicates on the original product to be rewritten after the
finite reindexing, without a choice-dependent coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrimeChoice_spec {n : Eisenstein} (h : (primaryPrimeFactors n).Nonempty) :
    largestPrimeChoice n ∈ primaryPrimeFactors n ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors n) (largestPrimeChoice n) := by
  simpa only [largestPrimeChoice,dite_eq_left h] using selectedLargestPrime_spec (primaryPrimeFactors n) h

lemma largestPrimeChoice_prime_mul {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c)
    (hl : largestPrimePredicate primeTieCode (primaryPrimeFactors c) p) :
    largestPrimeChoice (p*c) = p ∧ largestPrimeRemainder (p*c) = c := by
  have hf := primaryPrimeFactors_prime_mul hp hc hs hpc
  have hp_mem : p ∈ primaryPrimeFactors (p*c) := by rw [hf]; exact Finset.mem_insert_self _ _
  have hne : (primaryPrimeFactors (p*c)).Nonempty := ⟨p,hp_mem⟩
  have hlarge : largestPrimePredicate primeTieCode (primaryPrimeFactors (p*c)) p := by
    rw [hf]
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Or.inr ⟨rfl,le_rfl⟩
    · exact hl q hq
  have hchoice : largestPrimeChoice (p*c) = p :=
    largestPrime_unique primeTieCode_injective (largestPrimeChoice_spec hne).1 hp_mem
      (largestPrimeChoice_spec hne).2 hlarge
  refine ⟨hchoice,?_⟩
  have hnot : p ∉ primaryPrimeFactors c := fun h => hpc (primaryPrimeFactor_spec hc h).2
  rw [largestPrimeRemainder,hchoice,hf,Finset.erase_insert hnot,primaryPrimeFactors_prod hc hs]

lemma largestPrimeChoice_mul_eq_iff {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c) :
    largestPrimeChoice (p*c) = p ↔ largestPrimePredicate primeTieCode (primaryPrimeFactors c) p := by
  constructor
  · intro he q hq
    have hf := primaryPrimeFactors_prime_mul hp hc hs hpc
    have hmem : p ∈ primaryPrimeFactors (p*c) := by rw [hf]; exact Finset.mem_insert_self _ _
    have hl := (largestPrimeChoice_spec (show (primaryPrimeFactors (p*c)).Nonempty from ⟨p,hmem⟩)).2
    rw [he] at hl
    exact hl q (by rw [hf]; exact Finset.mem_insert_of_mem hq)
  · exact fun h => (largestPrimeChoice_prime_mul hp hc hs hpc h).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SelectedPrimeGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic after removing the selected largest prime. These
identities retain the original squarefreeness, exclusion and norm range. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma selectedPrime_product_conditions (r p c e : Eisenstein) (hp : primaryPrime p) :
    (Squarefree (r*(p*c)) ∧ IsCoprime (r*(p*c)) e) ↔
      Squarefree (r*c) ∧ IsCoprime (r*c) e ∧ IsCoprime p (c*(r*e)) := by
  have he : r*(p*c) = p*(r*c) := by ring
  rw [he,squarefree_mul_iff,IsCoprime.mul_left_iff]
  constructor
  · rintro ⟨⟨hpc,_,hsrc⟩,hpe,hrce⟩
    have hpc' : IsCoprime p (r*c) := isRelPrime_iff_isCoprime.mp hpc
    refine ⟨hsrc,hrce,?_⟩
    exact hpc'.of_mul_right_right.mul_right (hpc'.of_mul_right_left.mul_right hpe)
  · rintro ⟨hsrc,hrce,hpcre⟩
    have hpc : IsCoprime p (r*c) :=
      hpcre.of_mul_right_right.of_mul_right_left.mul_right hpcre.of_mul_right_left
    exact ⟨⟨hpc.isRelPrime,hp.2.irreducible.squarefree,hsrc⟩,
      hpcre.of_mul_right_right.of_mul_right_right,hrce⟩

lemma selectedPrime_norm_interval {r c : Eisenstein} (hr : r ≠ 0) (hc : c ≠ 0)
    (p : Eisenstein) (a b : ℝ) :
    (a < norm (r*(p*c)) ∧ norm (r*(p*c)) ≤ b) ↔
      a/norm (r*c) < norm p ∧ norm p ≤ b/norm (r*c) := by
  have hn : 0 < norm (r*c) := norm_pos_of_ne_zero (mul_ne_zero hr hc)
  have he : norm (r*(p*c)) = norm p*norm (r*c) := by
    rw [norm_mul_eq,norm_mul_eq,norm_mul_eq]
    ring
  rw [he]
  exact and_congr (div_lt_iff₀ hn).symm (le_div_iff₀ hn).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedIntervals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distinguished-coordinate stopping region is the
intersection of four norm bounds. All surrogate products here are
computed from the fixed selected divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometricPrimeSurrogate_pos {ρ B : ℝ} (hρ : 0 < ρ)
    (S : Finset Eisenstein) (bin : Eisenstein → ℕ) :
    0 < primeSurrogate S bin (geometricBinLower ρ B) := by
  unfold primeSurrogate
  exact Finset.prod_pos (fun p _ => pow_pos hρ _)

theorem stopped_distinguished_interval_iff {B ρ a b : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    {c d p : Eisenstein} (hc : primary c) (hd : primary d)
    (hp : primaryPrime p) (hpB : norm p ≤ B) :
    let S := primeSurrogate (primaryPrimeFactors d) (geometricPrimeBin ρ B) (geometricBinLower ρ B)
    let E := primeSurrogate (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ B) h)
      (geometricPrimeBin ρ B) (geometricBinLower ρ B)
    let P := geometricBinLower ρ B j
    (geometricPrimeBin ρ B p = j ∧
      (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
      stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early (c*p) d) ↔
    ((∀ q ∈ primaryPrimeFactors d, geometricPrimeBin ρ B q ≤ j₀) ∧
      (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ B) j₀).card = k) ∧
      (a/norm (c*d) < norm p ∧
      max P (Z/(norm c*S)) ≤ norm p ∧
      norm p < min (ρ*P) (min (Z*geometricBinLower ρ B j₀/(norm c*S))
        (if early = true then ρ*P else Q/(norm c*E))) ∧
      norm p ≤ b/norm (c*d)) := by
  dsimp only
  have hS := geometricPrimeSurrogate_pos (B := B) (zero_lt_one.trans hρ)
    (primaryPrimeFactors d) (geometricPrimeBin ρ B)
  have hE := geometricPrimeSurrogate_pos (B := B) (zero_lt_one.trans hρ)
    (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ B) h) (geometricPrimeBin ρ B)
  have hnorm : (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ↔
      a/norm (c*d) < norm p ∧ norm p ≤ b/norm (c*d) := by
    rw [mul_assoc]
    exact selectedPrime_norm_interval (primary_ne_zero hc) (primary_ne_zero hd) p a b
  rw [geometricPrimeBin_eq_iff hρ hρ₂ hj hp hpB,hnorm,
    stoppedSideTest_free_distinguished_interval (geometricPrimeBin ρ B) (geometricBinLower ρ B)
      j₀ k h Z Q early (primary_ne_zero hc) d p (pow_pos (zero_lt_one.trans hρ) _) hS hE]
  by_cases hearly : early = true
  · simp only [hearly,true_or,ite_true, if_true,max_le_iff,lt_min_iff]
    tauto
  · simp only [hearly,max_le_iff,lt_min_iff]
    tauto

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedDistinguishedRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime cancellation with the literal distinguished-coordinate bin,
output interval and both stopping tests. The interval is derived, not
assumed to describe the stopping support. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_stopped_distinguished_prime_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u M V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → 0 < z → 0 ≤ M → 0 ≤ V → |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ x, ‖W x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ c d v e : Eisenstein, primary c → primary d → v ≠ 0 →
      (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 → Real.log (norm e) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e,
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_distinguished_mixed_interval_saving hEF ℓ hℓ hA hD hH hE hF
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w z u M V j hT hρ hρ₂ hj hP hTP hw hz hM hV hu hMV W hW hWn hWd
    c d v e hc hd hv hnc hNv he hNe j₀ k h Z Q early
  let P := geometricBinLower ρ B j
  let S := primeSurrogate (primaryPrimeFactors d) (geometricPrimeBin ρ B) (geometricBinLower ρ B)
  let E₀ := primeSurrogate (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ B) h)
    (geometricPrimeBin ρ B) (geometricBinLower ρ B)
  let lo := a/norm (c*d)
  let low := max P (Z/(norm c*S))
  let up := min (ρ*P) (min (Z*geometricBinLower ρ B j₀/(norm c*S))
    (if early = true then ρ*P else Q/(norm c*E₀)))
  let hi := b/norm (c*d)
  let C := (∀ q ∈ primaryPrimeFactors d, geometricPrimeBin ρ B q ≤ j₀) ∧
    (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ B) j₀).card = k
  let U := ((primeCutoff B).filter (fun p => IsCoprime p e)).filter
    (fun p => largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p)
  let f := fun p => distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v
  have heq : (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e, f p) =
      if C then ∑ p ∈ U with lo < norm p ∧ low ≤ norm p ∧ norm p < up ∧ norm p ≤ hi, f p else 0 := by
    unfold stoppedDistinguishedPrimeSet
    simp only [U,Finset.sum_filter]
    by_cases hC : C
    · rw [ite_eq_left hC]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hcop : IsCoprime p e
      · by_cases hl : largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p
        · simp only [hcop,hl,ite_true, if_true]
          have hinterval := stopped_distinguished_interval_iff (a := a) (b := b) (j₀ := j₀) (k := k) (h := h) hρ hρ₂ hj Z Q early hc hd
            (mem_primeCutoff.mp hp).1 (mem_primeCutoff.mp hp).2
          have hi' : (geometricPrimeBin ρ B p = j ∧
              (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
              stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
                j₀ k h Z Q early (c*p) d) ↔
              lo < norm p ∧ low ≤ norm p ∧ norm p < up ∧ norm p ≤ hi := by
            constructor
            · intro hpred
              exact (hinterval.mp hpred).2
            · intro hq
              exact hinterval.mpr ⟨hC,hq⟩
          exact if_congr hi' rfl rfl
        · simp only [hcop,hl,ite_true, if_true,ite_false, if_false]
      · simp only [hcop,ite_false, if_false]
    · rw [ite_eq_right hC]
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hcop : IsCoprime p e
      · by_cases hl : largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p
        · simp only [hcop,hl,ite_true, if_true]
          apply ite_eq_right
          intro hpred
          have hinterval := stopped_distinguished_interval_iff (a := a) (b := b) (j₀ := j₀) (k := k) (h := h) hρ hρ₂ hj Z Q early hc hd
            (mem_primeCutoff.mp hp).1 (mem_primeCutoff.mp hp).2
          exact hC (hinterval.mp hpred).1
        · simp only [hcop,hl,ite_true, if_true,ite_false, if_false]
      · simp only [hcop,ite_false, if_false]
  have hPpos : 0 < P := zero_lt_one.trans (geometricBinLower_gt_one hρ hj)
  change ‖∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e, f p‖ ≤ _
  rw [heq]
  by_cases hC : C
  · rw [ite_eq_left hC]
    exact hbound T P B lo low up hi w z u M V hT hP hTP
      ((le_max_left _ _).trans (le_max_right _ _))
      ((min_le_left _ _).trans ((min_le_left _ _).trans
        (mul_le_mul_of_nonneg_right hρ₂ hPpos.le)))
      hw hz hM hV hu hMV W hW hWn hWd v e (primaryPrimeFactors (c*d)) hv hnc hNv he hNe
  · rw [ite_eq_right hC,norm_zero]
    positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedPrimeFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed complementary primary factor in a free-prime sum is a
constant of norm at most one, even when its cubic symbol vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_fixed_primary_free_prime_sum (ℓ : ℤ) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a : Eisenstein → ℂ)
    (r c v : Eisenstein) (hr : primary r) (hc : primary c) (u : ℝ) :
    (∑ p ∈ S, a p*normTwist u (r*(p*c))*angularCubicSymbol ℓ (r*(p*c)) v) =
      (normTwist u r*angularCubicSymbol ℓ r v)*
        ∑ p ∈ S, a p*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpc : p*c ≠ 0 := mul_ne_zero (hS p hp).2.ne_zero (primary_ne_zero hc)
  rw [normTwist_mul u (primary_ne_zero hr) hpc,
    angularCubicSymbol_mul_lower ℓ (primary_ne_zero hr) hpc]
  ring


lemma angular_fixed_primary_free_prime_norm (ℓ : ℤ) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a : Eisenstein → ℂ)
    (r c v : Eisenstein) (hr : primary r) (hc : primary c) (u : ℝ) :
    ‖∑ p ∈ S, a p*normTwist u (r*(p*c))*angularCubicSymbol ℓ (r*(p*c)) v‖ ≤
      ‖∑ p ∈ S, a p*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ := by
  rw [angular_fixed_primary_free_prime_sum ℓ S hS a r c v hr hc u,norm_mul,
    norm_mul,norm_normTwist,one_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (angularCubicSymbol_norm_le_one ℓ hr v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedFull
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the fixed complementary cubic character and the original
Möbius coefficient in the distinguished-coordinate prime sum. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedDistinguishedPrimeSet_primary (B ρ a b : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (c d e : Eisenstein) {p : Eisenstein}
    (hp : p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e) :
    primaryPrime p :=
  (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
    (Finset.mem_filter.mp hp).1).1).1).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedDistinguishedFull
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the fixed complementary cubic character and the original
Möbius coefficient in the distinguished-coordinate prime sum. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angular_distinguished_full_prime_norm (ℓ : ℤ) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (W : ℝ → ℂ) (w z u : ℝ)
    (c d v : Eisenstein) (hc : primary c) (hd : primary d) :
    ‖∑ p ∈ S, cutoffMoebius primeDetectorCutoff w d*
      distinguishedRadialWeight W w z (norm p)*normTwist u ((c*p)*d)*
        angularCubicSymbol ℓ ((c*p)*d) v‖ ≤
      ‖∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*
        mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ := by
  have hsplit : (∑ p ∈ S, cutoffMoebius primeDetectorCutoff w d*
      distinguishedRadialWeight W w z (norm p)*normTwist u ((c*p)*d)*
        angularCubicSymbol ℓ ((c*p)*d) v) =
      cutoffMoebius primeDetectorCutoff w d*
        ∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*normTwist u ((c*d)*(p*1))*
          angularCubicSymbol ℓ ((c*d)*(p*1)) v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have he : (c*p)*d = (c*d)*(p*1) := by ring
    rw [he]
    ring
  rw [hsplit,norm_mul]
  calc
    _ ≤ ‖∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*normTwist u ((c*d)*(p*1))*
          angularCubicSymbol ℓ ((c*d)*(p*1)) v‖ :=
      mul_le_of_le_one_left (_root_.norm_nonneg _) (primeDetectorCutoff_moebius_norm w d)
    _ ≤ ‖∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*normTwist u (p*1)*
          angularCubicSymbol ℓ (p*1) v‖ :=
      angular_fixed_primary_free_prime_norm ℓ S hS (fun p => distinguishedRadialWeight W w z (norm p))
        (c*d) 1 v (primary_mul hc hd) primary_one u
    _ = _ := by simp only [mul_one,normTwist_eq_mellinPhase]


theorem angular_stopped_distinguished_full_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u M V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → 0 < z → 0 ≤ M → 0 ≤ V → |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ x, ‖W x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ c d v e : Eisenstein, primary c → primary d → v ≠ 0 →
      (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      Real.log (norm (c*(d*e))) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)),
        cutoffMoebius primeDetectorCutoff w d*distinguishedRadialWeight W w z (norm p)*
          normTwist u ((c*p)*d)*angularCubicSymbol ℓ ((c*p)*d) v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_stopped_distinguished_prime_saving hEF ℓ hℓ hA hD hH hE hF
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w z u M V j hT hρ hρ₂ hj hP hTP hw hz hM hV hu hMV W hW hWn hWd
    c d v e hc hd hv hnc hNv he hNe j₀ k h Z Q early
  apply (angular_distinguished_full_prime_norm ℓ
    (stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)))
    (fun p hp => stoppedDistinguishedPrimeSet_primary B ρ a b j j₀ k h Z Q early c d (c*(d*e)) hp)
    W w z u c d v hc hd).trans
  exact hbound T B ρ a b w z u M V j hT hρ hρ₂ hj hP hTP hw hz hM hV hu hMV W hW hWn hWd
    c d v (c*(d*e)) hc hd hv hnc hNv
    (mul_ne_zero (primary_ne_zero hc) (mul_ne_zero (primary_ne_zero hd) he)) hNe
    j₀ k h Z Q early

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughDivisorBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished divisor is rough at a fixed power scale. On a
squarefree product this gives a uniform number of possible distinguished
divisors, stronger than the generic divisor bound for stopped beta. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem rough_primary_divisor_card (R : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {b : Eisenstein} (hb : primary b) (hs : Squarefree b)
    {w : ℝ} (hw : 1 ≤ w) (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : norm b < w^k) :
    (R.filter (fun r => r ∣ b)).card ≤ 2^k := by
  let T := R.filter (fun r => r ∣ b)
  let L := (primaryPrimeFactors b).filter (fun p => w ≤ norm p)
  have hS (r : Eisenstein) (hr : r ∈ T) : Squarefree r :=
    fun x hx => hs x (hx.trans (Finset.mem_filter.mp hr).2)
  have hL : L.card < k := primary_factor_subset_card_lt hb hs
    (Finset.filter_subset _ _) hw (fun p hp => (Finset.mem_filter.mp hp).2) hsize
  have hcard : T.card ≤ L.powerset.card := by
    apply Finset.card_le_card_of_injOn primaryPrimeFactors
    · intro r hr
      apply Finset.mem_powerset.mpr
      intro p hp
      have hp' := primaryPrimeFactor_spec (hR r (Finset.mem_filter.mp hr).1) hp
      exact Finset.mem_filter.mpr ⟨primaryPrime_mem_factors hb hp'.1
        (hp'.2.trans (Finset.mem_filter.mp hr).2),hrough r (Finset.mem_filter.mp hr).1 p hp⟩
    · intro r hr q hq he
      calc
        r = ∏ p ∈ primaryPrimeFactors r, p :=
          (primaryPrimeFactors_prod (hR r (Finset.mem_filter.mp hr).1) (hS r hr)).symm
        _ = ∏ p ∈ primaryPrimeFactors q, p := by rw [he]
        _ = q := primaryPrimeFactors_prod (hR q (Finset.mem_filter.mp hq).1) (hS q hq)
  exact hcard.trans (by rw [Finset.card_powerset]; exact Nat.pow_le_pow_right (by decide) hL.le)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedAbsoluteMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolute, uncollected complementary factorization mass used
after a free prime is cancelled. No cancellation inside beta is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rough_pairAbsolute_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (v f : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M)
    (hf : ∀ d ∈ D, ‖f d‖ ≤ 1) {b : Eisenstein}
    (hb : primary b) (hs : Squarefree b) {w : ℝ} (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : norm b < w^k) : pairAbsolute R D v f b ≤ (2^k:ℕ)*M := by
  calc
    _ ≤ ∑ _p ∈ primaryPairFiber R D b, M := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact (mul_le_mul_of_nonneg_left (hf p.2 hmem.2) (_root_.norm_nonneg _)).trans
        ((mul_one _).le.trans (hv p.1 hmem.1))
    _ = ((primaryPairFiber R D b).card:ℝ)*M := by simp
    _ ≤ ((R.filter (fun r => r ∣ b)).card:ℝ)*M :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (primaryPairFiber_card_le R D hR b)) hM
    _ ≤ (2^k:ℕ)*M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      (rough_primary_divisor_card R hR hb hs hw hrough hsize)) hM


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedComplementMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary pair mass after a selected-bin prime is removed.
The rough distinguished factor has only a bounded number of choices for
each squarefree product, so the total mass is linear in its norm range. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopped_complement_mass (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    (v : Eisenstein → ℂ) {M Y w : ℝ} (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : Y < w^k) :
    (∑ t ∈ (R ×ˢ D).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y),
      ‖v t.1‖) ≤ 18*Y*((2^k:ℕ)*M) := by
  let U := (R ×ˢ D).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y)
  let B := (primaryElementBall Y).filter Squarefree
  have hmap (t : Eisenstein × Eisenstein) (ht : t ∈ U) : t.1*t.2 ∈ B := by
    obtain ⟨ht,hpred⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
      ⟨primary_mul (hR _ hr) (hD _ hd),hpred.2⟩,hpred.1⟩
  have hfiber (b : Eisenstein) (hb : b ∈ B) :
      (∑ t ∈ U with t.1*t.2 = b, ‖v t.1‖) ≤ (2^k:ℕ)*M := by
    obtain ⟨hb,hs⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb,hbY⟩ := mem_primaryElementBall.mp hb
    have hsub : U.filter (fun t => t.1*t.2 = b) ⊆ primaryPairFiber R D b := by
      intro t ht
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,he⟩
    calc
      _ ≤ ∑ t ∈ primaryPairFiber R D b, ‖v t.1‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => _root_.norm_nonneg _)
      _ = pairAbsolute R D v (fun _ => 1) b := by
        simp only [pairAbsolute,norm_one,mul_one]
      _ ≤ _ := rough_pairAbsolute_bound R D hR v (fun _ => 1) hM hv
        (fun _ _ => by simp) hb hs hw hrough (hbY.trans_lt hsize)
  calc
    _ = ∑ b ∈ B, ∑ t ∈ U with t.1*t.2 = b, ‖v t.1‖ :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ _b ∈ B, (2^k:ℕ)*M := Finset.sum_le_sum hfiber
    _ = (B.card:ℝ)*((2^k:ℕ)*M) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (primaryElementBall_card_le hY))
      (mul_nonneg (Nat.cast_nonneg _) hM)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleCoordinate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing one distinguished coordinate is an exact finite bijection.
On squarefree prime tuples the largest-prime coordinate is unique. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma coordinateComplement_mem (S : ι → Finset Eisenstein) (i : ι) (g : ι → Eisenstein) :
    g ∈ coordinateComplementTuples S i ↔ g i = 1 ∧ ∀ j, j ≠ i → g j ∈ S j := by
  simp only [coordinateComplementTuples,Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · simpa only [Function.update_self,Finset.mem_singleton] using h i
    · intro j hj
      simpa only [Function.update_of_ne hj] using h j
  · rintro ⟨hi,h⟩ j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self,Finset.mem_singleton] using hi
    · simpa only [Function.update_of_ne hj] using h j hj

theorem primeTuple_coordinate_reindex (S : ι → Finset Eisenstein) (i : ι)
    (F : (ι → Eisenstein) → ℂ) :
    (∑ f ∈ Fintype.piFinset S, F f) =
      ∑ p ∈ S i, ∑ g ∈ coordinateComplementTuples S i, F (Function.update g i p) := by
  rw [←Finset.sum_product (S i) (coordinateComplementTuples S i)
    (fun t : Eisenstein × (ι → Eisenstein) => F (Function.update t.2 i t.1))]
  apply Finset.sum_bij (fun f _ => (f i,Function.update f i 1))
  · intro f hf
    refine Finset.mem_product.mpr ⟨(Fintype.mem_piFinset.mp hf) i,?_⟩
    apply (coordinateComplement_mem S i _).mpr
    refine ⟨Function.update_self _ _ _,?_⟩
    intro j hj
    simpa only [Function.update_of_ne hj] using (Fintype.mem_piFinset.mp hf) j
  · intro f hf g hg he
    have hp := congrArg Prod.fst he
    have hc := congrArg Prod.snd he
    dsimp only [Prod.fst] at hp
    dsimp only [Prod.snd] at hc
    calc
      f = Function.update (Function.update f i 1) i (f i) := by simp
      _ = Function.update (Function.update g i 1) i (g i) := by rw [hp,hc]
      _ = g := by simp
  · intro t ht
    obtain ⟨hp,hg⟩ := Finset.mem_product.mp ht
    obtain ⟨hgi,hgj⟩ := (coordinateComplement_mem S i t.2).mp hg
    refine ⟨Function.update t.2 i t.1,?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hp
      · simpa only [Function.update_of_ne hji] using hgj j hji
    · apply Prod.ext
      · exact Function.update_self _ _ _
      · rw [Function.update_idem,←hgi,Function.update_eq_self]
  · intro f hf
    simp only [Function.update_idem,Function.update_eq_self]

lemma primeTuple_update_product (f : ι → Eisenstein) (i : ι) (p : Eisenstein) :
    (∏ j, Function.update f i p j) = p*(∏ j ∈ Finset.univ.erase i, f j) := by
  rw [←Finset.mul_prod_erase Finset.univ (Function.update f i p) (Finset.mem_univ i),
    Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact Function.update_of_ne (Finset.mem_erase.mp hj).1 p f

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeComplementFibers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed multiplicity for the actual tuple remaining after a distinguished
coordinate is removed. The unit coordinate stays explicit. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementTuple_primary (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {g : ι → Eisenstein} (hg : g ∈ coordinateComplementTuples S i) :
    primary (∏ j, g j) := by
  obtain ⟨hgi,hg⟩ := (coordinateComplement_mem S i g).mp hg
  apply primary_finset_prod
  intro j _
  by_cases hj : j = i
  · simpa only [hj,hgi] using primary_one
  · exact (hS j (g j) (hg j hj)).1

lemma complementTuple_range_subset (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {f g : ι → Eisenstein} (hf : f ∈ coordinateComplementTuples S i)
    (hg : g ∈ coordinateComplementTuples S i)
    (hprod : (∏ j, g j) = ∏ j, f j) (j : ι) :
    g j ∈ Finset.univ.image f := by
  obtain ⟨hfi,hf⟩ := (coordinateComplement_mem S i f).mp hf
  obtain ⟨hgi,hg⟩ := (coordinateComplement_mem S i g).mp hg
  by_cases hji : j = i
  · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa only [hji,hgi] using hfi⟩
  · have hp := hS j (g j) (hg j hji)
    have hd : g j ∣ ∏ k, f k := hprod ▸ Finset.dvd_prod_of_mem g (Finset.mem_univ j)
    obtain ⟨k,_,hk⟩ := (hp.2.dvd_finsetProd_iff f).mp hd
    have hki : k ≠ i := by
      intro he
      rw [he,hfi] at hk
      exact hp.2.not_isUnit (isUnit_of_dvd_one hk)
    have hpk := hS k (f k) (hf k hki)
    have he : g j = f k := primary_associated_eq hp.1 hpk.1
      ((hp.2.dvd_prime_iff_associated hpk.2).mp hk)
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,he.symm⟩

theorem complementTuple_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι) (r : Eisenstein) :
    ((coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r)).card ≤
      (Fintype.card ι)^(Fintype.card ι) := by
  let T := (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r)
  by_cases hT : T.Nonempty
  · obtain ⟨f,hf⟩ := hT
    obtain ⟨hfs,hfr⟩ := Finset.mem_filter.mp hf
    have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.univ.image f) := by
      intro g hg
      obtain ⟨hgs,hgr⟩ := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      exact complementTuple_range_subset S hS i hfs hgs (hgr.trans hfr.symm)
    calc
      T.card ≤ (Fintype.piFinset (fun _ : ι => Finset.univ.image f)).card := Finset.card_le_card hsub
      _ = ((Finset.univ.image f).card)^(Fintype.card ι) := by simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left (by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := f))) _
  · change T.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    exact Nat.zero_le _

lemma complementTuple_prime_factor (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {g : ι → Eisenstein} (hg : g ∈ coordinateComplementTuples S i)
    {p : Eisenstein} (hp : primaryPrime p) (hpd : p ∣ ∏ j, g j) :
    ∃ j, j ≠ i ∧ p = g j := by
  obtain ⟨hgi,hg⟩ := (coordinateComplement_mem S i g).mp hg
  obtain ⟨j,_,hj⟩ := (hp.2.dvd_finsetProd_iff g).mp hpd
  have hji : j ≠ i := by
    intro he
    rw [he,hgi] at hj
    exact hp.2.not_isUnit (isUnit_of_dvd_one hj)
  exact ⟨j,hji,primary_associated_eq hp.1 (hS j (g j) (hg j hji)).1
    ((hp.2.dvd_prime_iff_associated (hS j (g j) (hg j hji)).2).mp hj)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplementAbsoluteWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative uncollected tuple weights. These retain the absolute
complementary mass; no cancellation of collected coefficients is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementAbsoluteWeight_nonneg (S : ι → Finset Eisenstein) (i : ι)
    (W : ι → Eisenstein → ℂ) (r : Eisenstein) :
    0 ≤ complementAbsoluteWeight S i W r :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => _root_.norm_nonneg _))

lemma complementAbsoluteWeight_bound (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) (hW : ∀ j, ∀ p ∈ S j, ‖W j p‖ ≤ 1) (r : Eisenstein) :
    complementAbsoluteWeight S i W r ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ) := by
  unfold complementAbsoluteWeight
  calc
    _ ≤ ∑ _g ∈ (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro g hg
      have hgs := (coordinateComplement_mem S i g).mp (Finset.mem_filter.mp hg).1
      apply Finset.prod_le_one (fun _ _ => _root_.norm_nonneg _)
      intro j hj
      exact hW j (g j) (hgs.2 j (Finset.mem_erase.mp hj).1)
    _ = (((coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r)).card:ℝ) := by simp
    _ ≤ _ := Nat.cast_le.mpr (complementTuple_fiber_card S hS i r)

lemma complementAbsoluteWeight_rough (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) {w : ℝ}
    (hrough : ∀ j, j ≠ i → ∀ p ∈ S j, W j p ≠ 0 → w ≤ norm p)
    {r p : Eisenstein} (hr : complementAbsoluteWeight S i W r ≠ 0)
    (hp : primaryPrime p) (hpr : p ∣ r) : w ≤ norm p := by
  obtain ⟨g,hg,hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  obtain ⟨hg,hgr⟩ := Finset.mem_filter.mp hg
  have hpd : p ∣ ∏ j, g j := by rw [hgr]; exact hpr
  obtain ⟨j,hji,hpj⟩ := complementTuple_prime_factor S hS i hg hp hpd
  have hnorm : ‖W j (g j)‖ ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩)
  have hWj : W j (g j) ≠ 0 := norm_ne_zero_iff.mp hnorm
  rw [hpj]
  exact hrough j hji (g j) (((coordinateComplement_mem S i g).mp hg).2 j hji) hWj

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplementAbsoluteMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear complementary mass after a distinguished prime is removed.
The absolute tuple weights are collected before applying rough divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementProductSupport_primary (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {r : Eisenstein} (hr : r ∈ complementProductSupport S i) : primary r := by
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hr
  exact complementTuple_primary S hS i hg

theorem complement_absolute_pair_mass (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) (hW : ∀ j, ∀ p ∈ S j, ‖W j p‖ ≤ 1)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) {Y w : ℝ}
    (hY : 0 ≤ Y) (hw : 1 ≤ w)
    (hrough : ∀ j, j ≠ i → ∀ p ∈ S j, W j p ≠ 0 → w ≤ norm p)
    {m : ℕ} (hsize : Y < w^m) :
    (∑ t ∈ (complementProductSupport S i ×ˢ D).filter
      (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y),
      complementAbsoluteWeight S i W t.1) ≤
      18*Y*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  let R := (complementProductSupport S i).filter
    (fun r => complementAbsoluteWeight S i W r ≠ 0)
  let f : Eisenstein → ℂ := fun r => (complementAbsoluteWeight S i W r : ℂ)
  have hf (r : Eisenstein) : ‖f r‖ = complementAbsoluteWeight S i W r := by
    simp only [f,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (complementAbsoluteWeight_nonneg S i W r)]
  have hbound := stopped_complement_mass R D
    (fun r hr => complementProductSupport_primary S hS i (Finset.mem_filter.mp hr).1) hD f
    (show 0 ≤ (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) by positivity) hY
    (fun r _ => by rw [hf]; exact complementAbsoluteWeight_bound S hS i W hW r) hw
    (fun r hr p hp => complementAbsoluteWeight_rough S hS i W hrough
      (Finset.mem_filter.mp hr).2
      (primaryPrimeFactor_spec
        (complementProductSupport_primary S hS i (Finset.mem_filter.mp hr).1) hp).1
      (primaryPrimeFactor_spec
        (complementProductSupport_primary S hS i (Finset.mem_filter.mp hr).1) hp).2) hsize
  simp only [hf] at hbound
  apply le_trans ?_ hbound
  apply le_of_eq
  symm
  apply Finset.sum_subset
  · intro t ht
    obtain ⟨ht,hcond⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hr).1,hd⟩,hcond⟩
  · intro t ht hn
    obtain ⟨ht,hcond⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    by_contra hne
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hr,hne⟩,hd⟩,hcond⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplementAbsoluteCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of absolute tuple weights by their primary product.
This is a finite identity, before any cancellation estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complement_absolute_collection (S : ι → Finset Eisenstein) (i : ι)
    (W : ι → Eisenstein → ℂ) (F : Eisenstein → ℝ) :
    (∑ g ∈ coordinateComplementTuples S i,
      (∏ j ∈ Finset.univ.erase i, ‖W j (g j)‖)*F (∏ j, g j)) =
    ∑ r ∈ complementProductSupport S i, complementAbsoluteWeight S i W r*F r := by
  calc
    _ = ∑ r ∈ complementProductSupport S i,
        ∑ g ∈ (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r),
          (∏ j ∈ Finset.univ.erase i, ‖W j (g j)‖)*F (∏ j, g j) := by
      exact (Finset.sum_fiberwise_of_maps_to
        (fun g hg => Finset.mem_image.mpr ⟨g,hg,rfl⟩) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      unfold complementAbsoluteWeight
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g hg
      rw [(Finset.mem_filter.mp hg).2]

theorem complement_absolute_tuple_mass (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) (hW : ∀ j, ∀ p ∈ S j, ‖W j p‖ ≤ 1)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) {Y w : ℝ}
    (hY : 0 ≤ Y) (hw : 1 ≤ w)
    (hrough : ∀ j, j ≠ i → ∀ p ∈ S j, W j p ≠ 0 → w ≤ norm p)
    {m : ℕ} (hsize : Y < w^m) :
    (∑ t ∈ (coordinateComplementTuples S i ×ˢ D).filter
      (fun t => Squarefree ((∏ j, t.1 j)*t.2) ∧ norm ((∏ j, t.1 j)*t.2) ≤ Y),
      ∏ j ∈ Finset.univ.erase i, ‖W j (t.1 j)‖) ≤
      18*Y*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  apply le_trans ?_ (complement_absolute_pair_mass S hS i W hW D hD hY hw hrough hsize)
  apply le_of_eq
  rw [Finset.sum_filter,Finset.sum_product,Finset.sum_filter,Finset.sum_product]
  rw [Finset.sum_comm,Finset.sum_comm (s := complementProductSupport S i)]
  apply Finset.sum_congr rfl
  intro d hd
  have hc := complement_absolute_collection S i W
    (fun r => if Squarefree (r*d) ∧ norm (r*d) ≤ Y then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero] using hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedComplementMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary tuple mass for the literal smooth distinguished
weights. Their rough support is proved from the detector difference. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma distinguishedRadialWeight_eq_primeWeight (W : ℝ → ℂ) (w z : ℝ) (p : Eisenstein) :
    distinguishedRadialWeight W w z (norm p) =
      W (norm p)*distinguishedPrimeWeight primeDetectorCutoff w z p := by
  simp only [distinguishedRadialWeight,distinguishedPrimeWeight,Complex.ofReal_sub]

lemma distinguishedRadialWeight_prime_rough (W : ℝ → ℂ) {w z : ℝ}
    (hw : 0 < w) (hwz : w ≤ z) {p : Eisenstein} (hp : primaryPrime p)
    (hne : distinguishedRadialWeight W w z (norm p) ≠ 0) : w < norm p := by
  rw [distinguishedRadialWeight_eq_primeWeight] at hne
  exact (distinguishedPrimeWeight_support
    (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx)
    hw hwz (norm_pos_of_ne_zero hp.2.ne_zero) (mul_ne_zero_iff.mp hne).2).1

theorem distinguished_complement_tuple_mass (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → ℝ → ℂ) (hW : ∀ j x, ‖W j x‖ ≤ 1)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) {Y w z : ℝ}
    (hY : 0 ≤ Y) (hw : 1 ≤ w) (hwz : w ≤ z)
    {m : ℕ} (hsize : Y < w^m) :
    (∑ t ∈ (coordinateComplementTuples S i ×ˢ D).filter
      (fun t => Squarefree ((∏ j, t.1 j)*t.2) ∧ norm ((∏ j, t.1 j)*t.2) ≤ Y),
      ∏ j ∈ Finset.univ.erase i,
        ‖distinguishedRadialWeight (W j) w z (norm (t.1 j))‖) ≤
      18*Y*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  apply complement_absolute_tuple_mass S hS i
    (fun j p => distinguishedRadialWeight (W j) w z (norm p)) ?_ D hD hY hw ?_ hsize
  · intro j p hp
    rw [distinguishedRadialWeight,norm_mul]
    exact (mul_le_mul (hW j (norm p)) (detector_difference_norm w z (norm p))
      (_root_.norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  · intro j _ p hp hne
    exact (distinguishedRadialWeight_prime_rough (W j)
      (zero_lt_one.trans_le hw) hwz (hS j p hp) hne).le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedPrimeGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original distinguished-coordinate conditions are exactly the
free-prime row conditions, including squarefreeness and the exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguished_prime_product_conditions (c p d e : Eisenstein)
    (hp : primaryPrime p) :
    (Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e) ↔
      Squarefree (c*d) ∧ IsCoprime (c*d) e ∧ IsCoprime p (c*(d*e)) := by
  have he : (c*p)*d = c*(p*d) := by ring
  have hf : d*(c*e) = c*(d*e) := by ring
  rw [he]
  simpa only [hf] using selectedPrime_product_conditions c p d e hp

lemma distinguished_largest_prime_iff {c p d : Eisenstein}
    (hc : primary c) (hp : primaryPrime p) (hd : primary d)
    (hs : Squarefree ((c*p)*d)) :
    largestPrimeChoice ((c*p)*d) = p ↔
      largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p := by
  have he : (c*p)*d = p*(c*d) := by ring
  rw [he] at hs ⊢
  have hcop : IsCoprime p (c*d) :=
    isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
  exact largestPrimeChoice_mul_eq_iff hp (primary_mul hc hd)
    (squarefree_mul_iff.mp hs).2.2
    (fun hdiv => hp.2.not_isUnit (hcop.isUnit_of_dvd hdiv))

lemma distinguished_prime_row_conditions {B ρ a b : ℝ} {j j₀ k h : ℕ}
    {Z Q : ℝ} {early : Bool} {c d e p : Eisenstein}
    (hc : primary c) (hd : primary d) (hp : p ∈ primeCutoff B) :
    (Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
      (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
      stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
        j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
      largestPrimeChoice ((c*p)*d) = p) ↔
    (Squarefree (c*d) ∧ IsCoprime (c*d) e ∧
      p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e))) := by
  constructor
  · rintro ⟨hs,hcop,hint,hstop,hbin,hlarge⟩
    obtain ⟨hscd,hcde,hpe⟩ := (distinguished_prime_product_conditions c p d e
      (mem_primeCutoff.mp hp).1).mp ⟨hs,hcop⟩
    refine ⟨hscd,hcde,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hp,hpe⟩,?_⟩,hbin,hint,hstop⟩⟩
    exact (distinguished_largest_prime_iff hc (mem_primeCutoff.mp hp).1 hd hs).mp hlarge
  · rintro ⟨hscd,hcde,hrow⟩
    obtain ⟨hp',hbin,hint,hstop⟩ := Finset.mem_filter.mp hrow
    obtain ⟨hp',hl⟩ := Finset.mem_filter.mp hp'
    obtain ⟨_,hpe⟩ := Finset.mem_filter.mp hp'
    obtain ⟨hs,hcop⟩ := (distinguished_prime_product_conditions c p d e
      (mem_primeCutoff.mp hp).1).mpr ⟨hscd,hcde,hpe⟩
    exact ⟨hs,hcop,hint,hstop,hbin,
      (distinguished_largest_prime_iff hc (mem_primeCutoff.mp hp).1 hd hs).mpr hl⟩

lemma stoppedDistinguished_complement_bound {B ρ a b : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {c d e p : Eisenstein} (hc : primary c) (hd : primary d)
    (hp : p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e) :
    norm (c*d) ≤ b/geometricBinLower ρ B j := by
  obtain ⟨hp',hbin,hint,_⟩ := Finset.mem_filter.mp hp
  have hpB := mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp').1).1
  have hnorm := (geometricPrimeBin_eq_iff hρ hρ₂ hj hpB.1 hpB.2).mp hbin
  have hn : 0 < norm (c*d) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero hc) (primary_ne_zero hd))
  apply (le_div_iff₀ (zero_lt_one.trans (geometricBinLower_gt_one hρ hj))).mpr
  calc
    norm (c*d)*geometricBinLower ρ B j ≤ norm (c*d)*norm p :=
      mul_le_mul_of_nonneg_left hnorm.1 hn.le
    _ = norm ((c*p)*d) := by simp only [norm_mul_eq]; ring
    _ ≤ b := hint.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedPrimeZero
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A distinguished prime row is empty outside its forced complementary
norm range. This keeps the later mass sum linear in the output length. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedDistinguished_row_eq_zero {B ρ a b : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {c d e : Eisenstein} (hc : primary c) (hd : primary d)
    (hbig : b/geometricBinLower ρ B j < norm (c*d)) (F : Eisenstein → ℂ) :
    (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e, F p) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  exact (not_lt_of_ge (stoppedDistinguished_complement_bound hρ hρ₂ hj hc hd hp) hbig).elim

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDistinguishedRowsSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summed distinguished-coordinate cancellation. The total complementary
mass is derived for the actual tuple weights and the actual norm cutoff. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_distinguished_rows_saving (i : ι) (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E F : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 ≤ b → 1 ≤ w → w ≤ z → 0 ≤ V → |u| ≤ T^H → 1+V ≤ T^F →
      b/geometricBinLower ρ B j < w^m →
      ∀ (S : ι → Finset Eisenstein) (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l, ∀ p ∈ S l, primaryPrime p) → (∀ l x, ‖W l x‖ ≤ 1) →
      ContDiff ℝ ∞ (W i) → (∀ x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ coordinateComplementTuples S i ×ˢ D₀,
        Squarefree ((∏ l, t.1 l)*t.2) → norm ((∏ l, t.1 l)*t.2) ≤ b/geometricBinLower ρ B j →
        Real.log (norm ((∏ l, t.1 l)*(t.2*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ t ∈ (coordinateComplementTuples S i ×ˢ D₀).filter
          (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧ IsCoprime ((∏ l, t.1 l)*t.2) e),
        (∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (t.1 l)))*
        (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
            (∏ l, t.1 l) t.2 ((∏ l, t.1 l)*(t.2*e)),
          cutoffMoebius primeDetectorCutoff w t.2*distinguishedRadialWeight (W i) w z (norm p)*
            normTwist u (((∏ l, t.1 l)*p)*t.2)*angularCubicSymbol ℓ (((∏ l, t.1 l)*p)*t.2) v)‖ ≤
        K*b/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_stopped_distinguished_full_saving hEF ℓ hℓ hA hD hH hE hF
  let C : ℝ := 18*((2^m:ℕ)*(((Fintype.card ι)^(Fintype.card ι):ℕ)+1))*K
  refine ⟨C,P₀,by dsimp [C]; positivity,hP₀,?_⟩
  intro T B ρ a b w z u V j hT hρ hρ₂ hj hP hTP hb hw hwz hV hu hVF hsize
    S W D₀ hS hW hWi hWd hD₀ v e hv hnc hNv he hNe j₀ k h Z Q early
  let P := geometricBinLower ρ B j
  let U := coordinateComplementTuples S i ×ˢ D₀
  let wt := fun t : (ι → Eisenstein) × Eisenstein =>
    ∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (t.1 l))
  let row := fun t : (ι → Eisenstein) × Eisenstein =>
    ∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
        (∏ l, t.1 l) t.2 ((∏ l, t.1 l)*(t.2*e)),
      cutoffMoebius primeDetectorCutoff w t.2*distinguishedRadialWeight (W i) w z (norm p)*
        normTwist u (((∏ l, t.1 l)*p)*t.2)*angularCubicSymbol ℓ (((∏ l, t.1 l)*p)*t.2) v
  let U₁ := U.filter (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧ norm ((∏ l, t.1 l)*t.2) ≤ b/P)
  have hPpos : 0 < P := zero_lt_one.trans (geometricBinLower_gt_one hρ hj)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hY : 0 ≤ b/P := div_nonneg hb hPpos.le
  have hrow (t : (ι → Eisenstein) × Eisenstein) (ht : t ∈ U₁) : ‖row t‖ ≤ K*P/T^D := by
    obtain ⟨ht,hs,hn⟩ := Finset.mem_filter.mp ht
    obtain ⟨hg,hd⟩ := Finset.mem_product.mp ht
    exact hbound T B ρ a b w z u 1 V j hT hρ hρ₂ hj hP hTP
      (zero_lt_one.trans_le hw) ((zero_lt_one.trans_le hw).trans_le hwz) (by norm_num)
      hV hu hVF (W i) hWi (hW i) hWd (∏ l, t.1 l) t.2 v e
      (complementTuple_primary S hS i hg) (hD₀ t.2 hd) hv hnc hNv he (hNe t ht hs hn)
      j₀ k h Z Q early
  have heq : (∑ t ∈ U.filter (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧
        IsCoprime ((∏ l, t.1 l)*t.2) e), wt t*row t) =
      ∑ t ∈ U₁, if IsCoprime ((∏ l, t.1 l)*t.2) e then wt t*row t else 0 := by
    simp only [U₁,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hg,hd⟩ := Finset.mem_product.mp ht
    by_cases hs : Squarefree ((∏ l, t.1 l)*t.2)
    · by_cases hn : norm ((∏ l, t.1 l)*t.2) ≤ b/P
      · by_cases hc : IsCoprime ((∏ l, t.1 l)*t.2) e <;> simp only [hs,hn,hc,and_self,ite_true, if_true,and_false,ite_false, if_false]
      · have hz : row t = 0 := stoppedDistinguished_row_eq_zero hρ hρ₂ hj
          (complementTuple_primary S hS i hg) (hD₀ t.2 hd) (lt_of_not_ge hn) _
        simp only [hs,hn,hz,and_false,mul_zero,ite_self]
    · simp only [hs,false_and,ite_false, if_false]
  change ‖∑ t ∈ U.filter (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧
    IsCoprime ((∏ l, t.1 l)*t.2) e), wt t*row t‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ t ∈ U₁, ‖wt t‖*(K*P/T^D) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro t ht
      split_ifs
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hrow t ht) (_root_.norm_nonneg _)
      · rw [norm_zero]
        positivity
    _ = (∑ t ∈ U₁, ‖wt t‖)*(K*P/T^D) := (Finset.sum_mul _ _ _).symm
    _ ≤ (18*(b/P)*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)))*(K*P/T^D) := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      simpa only [U₁,U,wt,norm_prod] using
        distinguished_complement_tuple_mass S hS i W hW D₀ hD₀ hY hw hwz hsize
    _ ≤ C*b/T^D := by
      have hmono : (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) ≤
          (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ)+1 := by linarith
      dsimp [C]
      have hscale : (18*(b/P)*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)))*(K*P/T^D) =
          (18*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ))*K)*b/T^D := by
        field_simp
      rw [hscale]
      gcongr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateRoles
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished largest-prime role splits into the actual tuple
coordinates with multiplicity one, even in the presence of the selected
divisor. No ordering of its prime factors is introduced. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma prime_tuple_divisor_indicator (f : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hi : Function.Injective f)
    {p : Eisenstein} (hp : primaryPrime p) (z : ℂ) :
    (if p ∣ ∏ i, f i then z else 0) = ∑ i, if p = f i then z else 0 := by
  by_cases hdiv : p ∣ ∏ i, f i
  · obtain ⟨i,_,hpi⟩ := (hp.2.dvd_finsetProd_iff f).mp hdiv
    have he : p = f i := primary_associated_eq hp.1 (hf i).1
      ((hp.2.dvd_prime_iff_associated (hf i).2).mp hpi)
    rw [ite_eq_left hdiv]
    symm
    calc
      _ = (if p = f i then z else 0) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          have hne : ¬p = f j := fun hpj => hji (hi (hpj.symm.trans he))
          exact ite_eq_right hne
        · intro hnot
          exact (hnot (Finset.mem_univ i)).elim
      _ = z := ite_eq_left he
  · rw [ite_eq_right hdiv]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro he
    apply hdiv
    rw [he]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)

/-- A squarefree full product has exactly one distinguished coordinate
when its canonical largest prime lies on the distinguished side. -/
theorem distinguished_largest_coordinate_roles [Nonempty ι]
    (f : ι → Eisenstein) (hf : ∀ i, primaryPrime (f i))
    {d : Eisenstein} (hd : primary d) (hs : Squarefree ((∏ i, f i)*d)) (z : ℂ) :
    (if largestPrimeChoice ((∏ i, f i)*d) ∣ ∏ i, f i then z else 0) =
      ∑ i, if largestPrimeChoice ((∏ i, f i)*d) = f i then z else 0 := by
  have hr : primary (∏ i, f i) :=
    primary_finset_prod Finset.univ f (fun i _ => (hf i).1)
  have hi := (squarefree_prime_tuple_iff f hf).mp (squarefree_mul_iff.mp hs).2.1
  let i : ι := Classical.arbitrary ι
  have him : f i ∈ primaryPrimeFactors ((∏ j, f j)*d) :=
    (primaryPrime_mem_factors_iff (primary_mul hr hd)).mpr
      ⟨hf i,(Finset.dvd_prod_of_mem f (Finset.mem_univ i)).trans (dvd_mul_right _ _)⟩
  have hne : (primaryPrimeFactors ((∏ j, f j)*d)).Nonempty := ⟨f i,him⟩
  exact prime_tuple_divisor_indicator f hf hi
    (primaryPrimeFactor_spec (primary_mul hr hd) (largestPrimeChoice_spec hne).1).1 z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedCoordinateReindex
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact free-coordinate expansion of the distinguished largest-prime
role. The global largest prime is retained, including the selected divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeTuple_update_weight (f : ι → Eisenstein) (i : ι) (p : Eisenstein)
    (w : ι → Eisenstein → ℂ) :
    (∏ j, w j (Function.update f i p j)) = w i p*(∏ j ∈ Finset.univ.erase i, w j (f j)) := by
  rw [←Finset.mul_prod_erase Finset.univ (fun j => w j (Function.update f i p j))
    (Finset.mem_univ i),Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem distinguished_tuple_largest_reindex [Nonempty ι]
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    {d : Eisenstein} (hd : primary d) (F : (ι → Eisenstein) → ℂ) :
    (∑ f ∈ (Fintype.piFinset S).filter (fun f => Squarefree ((∏ i, f i)*d)),
      if largestPrimeChoice ((∏ i, f i)*d) ∣ ∏ i, f i then F f else 0) =
      ∑ i, ∑ g ∈ coordinateComplementTuples S i, ∑ p ∈ S i,
        if Squarefree ((∏ j, Function.update g i p j)*d) ∧
          largestPrimeChoice ((∏ j, Function.update g i p j)*d) = p
        then F (Function.update g i p) else 0 := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ f ∈ Fintype.piFinset S, ∑ i,
        if Squarefree ((∏ j, f j)*d) ∧ largestPrimeChoice ((∏ j, f j)*d) = f i
        then F f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hs : Squarefree ((∏ j, f j)*d)
      · simpa only [hs,ite_true, if_true,true_and] using
          distinguished_largest_coordinate_roles f
            (fun i => hS i (f i) ((Fintype.mem_piFinset.mp hf) i)) hd hs (F f)
      · simp only [hs,false_and,ite_false, if_false,Finset.sum_const_zero]
    _ = ∑ i, ∑ f ∈ Fintype.piFinset S,
        if Squarefree ((∏ j, f j)*d) ∧ largestPrimeChoice ((∏ j, f j)*d) = f i
        then F f else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [primeTuple_coordinate_reindex S i]
      rw [Finset.sum_comm]
      simp only [Function.update_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedPrimeCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite collection of the distinguished-coordinate conditions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedDistinguishedPrimeSet_subset (B ρ a b : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (c d e : Eisenstein) :
    stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e ⊆ primeCutoff B := by
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1

theorem distinguished_prime_collection (B ρ a b : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (c d e : Eisenstein)
    (hc : primary c) (hd : primary d) (F : Eisenstein → ℂ) :
    (∑ p ∈ primeCutoff B,
      if Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
        (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
        stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
          j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
        largestPrimeChoice ((c*p)*d) = p then F p else 0) =
    if Squarefree (c*d) ∧ IsCoprime (c*d) e then
      ∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)), F p
    else 0 := by
  calc
    _ = ∑ p ∈ primeCutoff B,
        if Squarefree (c*d) ∧ IsCoprime (c*d) e ∧
          p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e))
        then F p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact if_congr (distinguished_prime_row_conditions hc hd hp) rfl rfl
    _ = _ := by
      by_cases hcd : Squarefree (c*d) ∧ IsCoprime (c*d) e
      · rw [ite_eq_left hcd]
        have he (p : Eisenstein) :
            (Squarefree (c*d) ∧ IsCoprime (c*d) e ∧
              p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e))) ↔
            p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)) := by
          constructor
          · exact fun hp => hp.2.2
          · exact fun hp => ⟨hcd.1,hcd.2,hp⟩
        simp_rw [if_congr (he _) rfl rfl]
        rw [←Finset.sum_filter,Finset.filter_mem_eq_of_subset
          (stoppedDistinguishedPrimeSet_subset B ρ a b j j₀ k h Z Q early c d (c*(d*e)))]
      · rw [ite_eq_right hcd]
        apply Finset.sum_eq_zero
        intro p hp
        exact ite_eq_right (fun hpred => hcd ⟨hpred.1,hpred.2.1⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedTupleRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original distinguished-role tuple sum is exactly the sum of the
free-prime rows; the global largest-prime and stopping tests are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementTuple_update_product (S : ι → Finset Eisenstein) (i : ι)
    {g : ι → Eisenstein} (hg : g ∈ coordinateComplementTuples S i) (p : Eisenstein) :
    (∏ l, Function.update g i p l) = (∏ l, g l)*p := by
  have hgi := ((coordinateComplement_mem S i g).mp hg).1
  have he : (∏ l, g l) = ∏ l ∈ Finset.univ.erase i, g l := by
    rw [←Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i),hgi,one_mul]
  rw [primeTuple_update_product,he,mul_comm]

theorem distinguished_tuple_stopped_rows [Nonempty ι]
    (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (d e : Eisenstein) (hd : primary d) (w : ι → Eisenstein → ℂ) (G : Eisenstein → ℂ) :
    (∑ f ∈ (Fintype.piFinset (fun _ : ι => primeCutoff B)).filter
        (fun f => Squarefree ((∏ l, f l)*d)),
      if largestPrimeChoice ((∏ l, f l)*d) ∣ ∏ l, f l then
        if IsCoprime ((∏ l, f l)*d) e ∧
          (a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b) ∧
          stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
            j₀ k h Z Q early (∏ l, f l) d ∧
          geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j
        then (∏ l, w l (f l))*G ((∏ l, f l)*d) else 0
      else 0) =
    ∑ i, ∑ g ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i,
      (∏ l ∈ Finset.univ.erase i, w l (g l))*
      (if Squarefree ((∏ l, g l)*d) ∧ IsCoprime ((∏ l, g l)*d) e then
        ∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
            (∏ l, g l) d ((∏ l, g l)*(d*e)), w i p*G (((∏ l, g l)*p)*d)
      else 0) := by
  rw [distinguished_tuple_largest_reindex (fun _ : ι => primeCutoff B)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) hd]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro g hg
  let c := ∏ l, g l
  have hc : primary c := complementTuple_primary (fun _ : ι => primeCutoff B)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) i hg
  calc
    _ = (∏ l ∈ Finset.univ.erase i, w l (g l))*
        ∑ p ∈ primeCutoff B,
          if Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
            (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
            largestPrimeChoice ((c*p)*d) = p then w i p*G ((c*p)*d) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [complementTuple_update_product _ i hg p,primeTuple_update_weight]
      change (if Squarefree ((c*p)*d) ∧ largestPrimeChoice ((c*p)*d) = p then
        if IsCoprime ((c*p)*d) e ∧ (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B (largestPrimeChoice ((c*p)*d)) = j
          then (w i p*(∏ l ∈ Finset.univ.erase i, w l (g l)))*G ((c*p)*d) else 0
        else 0) = _
      rw [←ite_and]
      have he : ((Squarefree ((c*p)*d) ∧ largestPrimeChoice ((c*p)*d) = p) ∧
          (IsCoprime ((c*p)*d) e ∧ (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B (largestPrimeChoice ((c*p)*d)) = j)) ↔
          (Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
            (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
            largestPrimeChoice ((c*p)*d) = p) := by
        constructor
        · rintro ⟨⟨hs,he⟩,hc,hrange,hstop,hbin⟩
          rw [he] at hbin
          exact ⟨hs,hc,hrange,hstop,hbin,he⟩
        · rintro ⟨hs,hc,hrange,hstop,hbin,he⟩
          exact ⟨⟨hs,he⟩,hc,hrange,hstop,by simpa only [he] using hbin⟩
      have hh := if_congr he
        (Eq.refl ((w i p*(∏ l ∈ Finset.univ.erase i, w l (g l)))*G ((c*p)*d)))
        (Eq.refl (0:ℂ))
      apply hh.trans
      split_ifs <;> ring
    _ = _ := by
      rw [distinguished_prime_collection B ρ a b j j₀ k h Z Q early c d e hc hd]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedTupleCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the literal stopped beta into its ordered prime
tuples and independent selected divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_tuple_sum (S : ι → Finset Eisenstein)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ) (D : Finset Eisenstein)
    (selected : Eisenstein → Eisenstein → Prop) (K : Eisenstein → ℂ) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport S) D,
      stoppedBeta (orderedConvolutionSupport S) D (distinguishedTupleCoefficient S W ψ w z)
        ψ w selected n*K n) =
    ((Fintype.card ι).factorial:ℂ)⁻¹ *
      ∑ d ∈ D, ∑ f ∈ Fintype.piFinset S,
        if selected (∏ i, f i) d then
          (∏ i, W i (f i)*distinguishedPrimeWeight ψ w z (f i))*
            cutoffMoebius ψ w d*K ((∏ i, f i)*d) else 0 := by
  unfold stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  calc
    _ = ((Fintype.card ι).factorial:ℂ)⁻¹ *
        ∑ r ∈ orderedConvolutionSupport S,
          orderedConvolution S (fun i p => W i p*distinguishedPrimeWeight ψ w z p) r *
            ∑ d ∈ D, if selected r d then cutoffMoebius ψ w d*K (r*d) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hs : selected r d
      · simp only [hs,ite_true, if_true,distinguishedTupleCoefficient]
        ring
      · simp only [hs,ite_false, if_false,zero_mul,mul_zero]
    _ = _ := by
      rw [orderedConvolution_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hs : selected (∏ i, f i) d
      · simp only [hs,ite_true, if_true]
        ring
      · simp only [hs,ite_false, if_false,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedDistinguishedIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished largest-prime role of literal stopped beta,
with the ordered-tuple factorial and original full-product twist. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stoppedBeta_distinguished_original_tuple (ℓ : ℤ) (B ρ a b w z u : ℝ)
    (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (W : ι → ℝ → ℂ) (D : Finset Eisenstein) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D,
      stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
          (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*angularCubicSymbol ℓ n v else 0)) =
    ((Fintype.card ι).factorial:ℂ)⁻¹ * ∑ d ∈ D,
      ∑ f ∈ (Fintype.piFinset (fun _ : ι => primeCutoff B)).filter
          (fun f => Squarefree ((∏ l, f l)*d)),
        if largestPrimeChoice ((∏ l, f l)*d) ∣ ∏ l, f l then
          if IsCoprime ((∏ l, f l)*d) e ∧
            (a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (∏ l, f l) d ∧
            geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j
          then (∏ l, distinguishedRadialWeight (W l) w z (norm (f l)))*
            (cutoffMoebius primeDetectorCutoff w d*normTwist u ((∏ l, f l)*d)*
              angularCubicSymbol ℓ ((∏ l, f l)*d) v) else 0
        else 0 := by
  rw [stoppedBeta_distinguished_tuple_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f hf
  have hprod : (∏ l, W l (norm (f l))*distinguishedPrimeWeight primeDetectorCutoff w z (f l)) =
      ∏ l, distinguishedRadialWeight (W l) w z (norm (f l)) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact (distinguishedRadialWeight_eq_primeWeight (W l) w z (f l)).symm
  rw [hprod]
  simp only [stoppedDistinguishedTest,mul_ite,mul_zero]
  rw [←ite_and,←ite_and,←ite_and]
  have he : ((stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
        j₀ k h Z Q early (∏ l, f l) d ∧ largestPrimeChoice ((∏ l, f l)*d) ∣ (∏ l, f l) ∧
        geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j) ∧
      (Squarefree ((∏ l, f l)*d) ∧ IsCoprime ((∏ l, f l)*d) e ∧
        a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b)) ↔
    ((Squarefree ((∏ l, f l)*d) ∧
      largestPrimeChoice ((∏ l, f l)*d) ∣ (∏ l, f l)) ∧
        (IsCoprime ((∏ l, f l)*d) e ∧
          (a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b) ∧
          stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
            j₀ k h Z Q early (∏ l, f l) d ∧
          geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j)) := by tauto
  apply (if_congr he rfl rfl).trans
  split_ifs <;> ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedDistinguishedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the literal distinguished stopped coefficient into
the prime rows whose cancellation has already been proved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem angular_stoppedBeta_distinguished_rows (ℓ : ℤ) [Nonempty ι] (B ρ a b w z u : ℝ)
    (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (W : ι → ℝ → ℂ) (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d)
    (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D,
      stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
          (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*angularCubicSymbol ℓ n v else 0)) =
    ((Fintype.card ι).factorial:ℂ)⁻¹ *
      ∑ i, angular_stoppedDistinguishedRows ℓ B ρ a b w z u j j₀ k h Z Q early W D v e i := by
  rw [angular_stoppedBeta_distinguished_original_tuple ℓ]
  congr 1
  calc
    _ = ∑ d ∈ D, ∑ i,
        ∑ g ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i,
          if Squarefree ((∏ l, g l)*d) ∧ IsCoprime ((∏ l, g l)*d) e then
            (∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (g l)))*
              (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
                  (∏ l, g l) d ((∏ l, g l)*(d*e)),
                cutoffMoebius primeDetectorCutoff w d*
                  distinguishedRadialWeight (W i) w z (norm p)*
                  normTwist u (((∏ l, g l)*p)*d)*angularCubicSymbol ℓ (((∏ l, g l)*p)*d) v)
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [distinguished_tuple_stopped_rows B ρ a b j j₀ k h Z Q early d e (hD d hd)
        (fun l p => distinguishedRadialWeight (W l) w z (norm p))
        (fun n => cutoffMoebius primeDetectorCutoff w d*normTwist u n*angularCubicSymbol ℓ n v)]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro g hg
      split_ifs
      · congr 1
        apply Finset.sum_congr rfl
        intro p hp
        ring
      · rw [mul_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      simp only [angular_stoppedDistinguishedRows, Finset.sum_filter, Finset.sum_product]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedDistinguishedSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation for the literal distinguished role in the stopped beta
coefficient, with the ordered-tuple factorial retained. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_stoppedBeta_distinguished_saving (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E F : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 ≤ b → 1 ≤ w → w ≤ z → 0 ≤ V → |u| ≤ T^H → 1+V ≤ T^F →
      b/geometricBinLower ρ B j < w^m →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ i, ∀ t ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i ×ˢ D₀,
        Squarefree ((∏ l, t.1 l)*t.2) → norm ((∏ l, t.1 l)*t.2) ≤ b/geometricBinLower ρ B j →
        Real.log (norm ((∏ l, t.1 l)*(t.2*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/T^D := by
  choose C P hC hP hbound using fun i : ι =>
    angular_stopped_distinguished_rows_saving i m hEF ℓ hℓ hA hD hH hE hF
  let q : ℝ := ‖((Fintype.card ι).factorial:ℂ)⁻¹‖
  let K : ℝ := q*(∑ i, C i)+1
  let P₀ : ℝ := 2+∑ i, |P i|
  have hK : 0 < K := by
    have hs : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    have hq : 0 ≤ q := _root_.norm_nonneg _
    dsimp [K]
    nlinarith [mul_nonneg hq hs]
  have hP₀ : 1 < P₀ := by
    dsimp [P₀]
    have hn : 0 ≤ ∑ i, |P i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w z u V j hT hρ hρ₂ hj hp hTP hb hw hwz hV hu hVF hsize
    W D₀ hW hWi hWd hD₀ v e hv hnc hNv he hNe j₀ k h Z Q early
  have hiP (i : ι) : P i ≤ geometricBinLower ρ B j := by
    apply le_trans ?_ hp
    calc
      P i ≤ |P i| := le_abs_self _
      _ ≤ ∑ l, |P l| := Finset.single_le_sum
        (f := fun l : ι => |P l|) (fun l _ => abs_nonneg (P l)) (Finset.mem_univ i)
      _ ≤ P₀ := by dsimp [P₀]; linarith
  have hrow (i : ι) :
      ‖angular_stoppedDistinguishedRows ℓ B ρ a b w z u j j₀ k h Z Q early W D₀ v e i‖ ≤ C i*b/T^D := by
    exact hbound i T B ρ a b w z u V j hT hρ hρ₂ hj (hiP i) hTP hb hw hwz hV hu hVF hsize
      (fun _ : ι => primeCutoff B) W D₀ (fun _ _ h => (mem_primeCutoff.mp h).1)
      hW (hWi i) (hWd i) hD₀ v e hv hnc hNv he (hNe i) j₀ k h Z Q early
  rw [angular_stoppedBeta_distinguished_rows ℓ B ρ a b w z u j j₀ k h Z Q early W D₀ hD₀ v e,norm_mul]
  change q*‖∑ i, angular_stoppedDistinguishedRows ℓ B ρ a b w z u j j₀ k h Z Q early W D₀ v e i‖ ≤ _
  calc
    _ ≤ q*∑ i, ‖angular_stoppedDistinguishedRows ℓ B ρ a b w z u j j₀ k h Z Q early W D₀ v e i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (_root_.norm_nonneg _)
    _ ≤ q*∑ i, C i*b/T^D :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hrow i)) (_root_.norm_nonneg _)
    _ = (q*∑ i, C i)*b/T^D := by rw [←Finset.sum_div,←Finset.sum_mul]; ring
    _ ≤ K*b/T^D := by
      apply div_le_div_of_nonneg_right ?_ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hT) _).le
      apply mul_le_mul_of_nonneg_right ?_ hb
      dsimp [K]
      linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeLogScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-prime threshold gives the actual logarithmic parameter
range required by the published prime estimate, even after bin dilation. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem long_prime_logarithmic_window {P₀ : ℝ} (hP₀ : 1 < P₀) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X/4 ∧
      ∀ P : ℝ, Real.exp (Real.sqrt (Real.log X))/2 ≤ P →
        P₀ ≤ P ∧ Real.log X/4 ≤ (Real.log P)^2 := by
  have ht : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop
    (max (2*Real.log 2) (Real.log (2*P₀)))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))] with X hroot hL
  have hroot₂ : 2*Real.log 2 ≤ Real.sqrt (Real.log X) := (le_max_left _ _).trans hroot
  have hrootP : Real.log (2*P₀) ≤ Real.sqrt (Real.log X) := (le_max_right _ _).trans hroot
  refine ⟨by linarith,?_⟩
  intro P hP
  have hPpos : 0 < P := (div_pos (Real.exp_pos _) (by norm_num)).trans_le hP
  have hP₀pos : 0 < 2*P₀ := by linarith
  refine ⟨?_,?_⟩
  · calc
      P₀ = Real.exp (Real.log (2*P₀))/2 := by rw [Real.exp_log hP₀pos]; ring
      _ ≤ Real.exp (Real.sqrt (Real.log X))/2 :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hrootP) (by norm_num)
      _ ≤ P := hP
  · have hlog : Real.sqrt (Real.log X)-Real.log 2 ≤ Real.log P := by
      have h := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num)) hP
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num),Real.log_exp] at h
      exact h
    have hhalf : Real.sqrt (Real.log X)/2 ≤ Real.log P := by linarith
    have hlog₀ : 0 ≤ Real.log P := (by positivity : 0 ≤ Real.sqrt (Real.log X)/2).trans hhalf
    have hprod := mul_nonneg (sub_nonneg.mpr hhalf)
      (add_nonneg hlog₀ (by positivity : 0 ≤ Real.sqrt (Real.log X)/2))
    have hsqrt := Real.sq_sqrt (show 0 ≤ Real.log X by linarith)
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeParameterScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed powers of log X fit the prime parameter log X/4 after a
one-unit exponent enlargement. This is uniform in all arithmetic data. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_log_parameter_power (c A : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      0 < Real.log X/4 ∧ c*(Real.log X)^A ≤ (Real.log X/4)^(A+1) := by
  have ht : Tendsto (fun X : ℝ => Real.log X/4) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num : (0:ℝ) < 4)
  filter_upwards [ht.eventually (eventually_ge_atTop (max 1 (c*4^A)))] with X hX
  have hT : 0 < Real.log X/4 := zero_lt_one.trans_le ((le_max_left _ _).trans hX)
  refine ⟨hT,?_⟩
  have he : Real.log X = 4*(Real.log X/4) := by ring
  calc
    c*(Real.log X)^A = (c*4^A)*(Real.log X/4)^A := by
      conv_lhs => rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hT.le]
      ring
    _ ≤ (Real.log X/4)*(Real.log X/4)^A :=
      mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hX) (Real.rpow_nonneg hT.le _)
    _ = (Real.log X/4)^(A+1) := by
      rw [Real.rpow_add hT,Real.rpow_one]
      ring

lemma prime_parameter_log_saving {L D b : ℝ} (hL : 0 < L) :
    b/(L/4)^D = 4^D*b/L^D := by
  rw [Real.div_rpow hL.le (by norm_num : (0:ℝ) ≤ 4)]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimeScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual complementary norm and exclusion bounds needed to put
stopped prime rows on the parameter log X/4. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_complement_power_bound {X C ξ P b : ℝ} {m : ℕ}
    (hX : 1 < X) (hgap : C < ξ*m) (hb : 0 ≤ b) (hbX : b ≤ X^C) (hP : 1 ≤ P) :
    b/P < (X^ξ)^m := by
  calc
    b/P ≤ b := div_le_self hb hP
    _ ≤ X^C := hbX
    _ < X^(ξ*m) := Real.rpow_lt_rpow_of_exponent_lt hX hgap
    _ = (X^ξ)^m := by rw [←Real.rpow_mul_natCast (zero_lt_one.trans hX).le]

lemma stopped_complement_exclusion_log {r d e : Eisenstein} (hr : primary r)
    (hd : primary d) (he : e ≠ 0) {X C E b P : ℝ} (hX : 0 < X)
    (hb : 0 ≤ b) (hbX : b ≤ X^C) (hP : 1 ≤ P)
    (hrd : norm (r*d) ≤ b/P) (heX : norm e ≤ X^E) :
    Real.log (norm (r*(d*e))) ≤ (C+E)*Real.log X := by
  have hrp : 0 < norm (r*d) := zero_lt_one.trans_le
    (one_le_norm (primary_ne_zero (primary_mul hr hd)))
  have hep : 0 < norm e := zero_lt_one.trans_le (one_le_norm he)
  have hrX : norm (r*d) ≤ X^C := hrd.trans ((div_le_self hb hP).trans hbX)
  calc
    Real.log (norm (r*(d*e))) = Real.log (norm (r*d))+Real.log (norm e) := by
      rw [←mul_assoc,norm_mul_eq,Real.log_mul (ne_of_gt hrp) (ne_of_gt hep)]
    _ ≤ Real.log (X^C)+Real.log (X^E) :=
      add_le_add (Real.log_le_log hrp hrX) (Real.log_le_log hep heX)
    _ = (C+E)*Real.log X := by rw [Real.log_rpow hX,Real.log_rpow hX]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedDistinguishedLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform log-X saving for the literal distinguished role. Polynomial
exclusions and the complementary roughness condition are derived from
their actual norm bounds, rather than added prime-row assumptions. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_stoppedBeta_distinguished_log_saving (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E F C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u V : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      0 ≤ b → b ≤ X^C → X^ξ ≤ z → 0 ≤ V →
      |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_stoppedBeta_distinguished_saving (ι := ι) m hEF ℓ hℓ
    (A := A+1) (D := D) (H := H+1) (E := 2) (F := F+1)
    (by linarith) hD (by linarith) (by norm_num) (by linarith)
  refine ⟨K*4^D,by positivity,?_⟩
  filter_upwards [long_prime_logarithmic_window hP₀,
    eventually_log_parameter_power 1 A,eventually_log_parameter_power 1 H,
    eventually_log_parameter_power 1 F,eventually_log_parameter_power (C+E) 1,
    eventually_gt_atTop (1:ℝ)] with X hwindow hscaleA hscaleH hscaleF hscaleE hX
  intro B ρ a b z u V j hρ hρ₂ hj hPlong hb hbX hwz hV hu hVF
    W D₀ hW hWi hWd hD₀ v e hv hnc hNv he heX j₀ k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLp : 0 < Real.log X := Real.log_pos hX
  have hP := hwindow.2 _ hPlong
  have hw : 1 ≤ X^ξ := Real.one_le_rpow hX.le hξ.le
  have hsize : b/geometricBinLower ρ B j < (X^ξ)^m :=
    stopped_complement_power_bound hX hgap hb hbX (geometricBinLower_gt_one hρ hj).le
  have hNe (i : ι) (t : (ι → Eisenstein) × Eisenstein)
      (ht : t ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i ×ˢ D₀)
      (_hs : Squarefree ((∏ l, t.1 l)*t.2))
      (hn : norm ((∏ l, t.1 l)*t.2) ≤ b/geometricBinLower ρ B j) :
      Real.log (norm ((∏ l, t.1 l)*(t.2*e))) ≤ (Real.log X/4)^(2:ℝ) := by
    obtain ⟨hg,hd⟩ := Finset.mem_product.mp ht
    have hprod := complementTuple_primary (fun _ : ι => primeCutoff B)
      (fun _ _ hp => (mem_primeCutoff.mp hp).1) i hg
    apply (stopped_complement_exclusion_log hprod (hD₀ _ hd) he hXp hb hbX
      (geometricBinLower_gt_one hρ hj).le hn heX).trans
    simpa only [Real.rpow_one,show (1:ℝ)+1=2 by norm_num] using hscaleE.2
  have hh := hbound (Real.log X/4) B ρ a b (X^ξ) z u V j hwindow.1 hρ hρ₂ hj
    hP.1 hP.2 hb hw hwz hV (hu.trans (by simpa only [one_mul] using hscaleH.2))
    (hVF.trans (by simpa only [one_mul] using hscaleF.2)) hsize W D₀ hW hWi hWd hD₀
    v e hv hnc (hNv.trans (by simpa only [one_mul] using hscaleA.2)) he hNe
    j₀ k h Z Q early
  apply hh.trans_eq
  rw [prime_parameter_log_saving hLp]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLargestRoles
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact splitting of a valid largest-prime bin into its distinguished
and selected-divisor roles. The source stopping test is unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrimeChoice_prime_of_bin {B ρ : ℝ} {j : ℕ}
    (hj : j < geometricBinCount ρ B) {n : Eisenstein} (hn : primary n)
    (hbin : geometricPrimeBin ρ B (largestPrimeChoice n) = j) :
    primaryPrime (largestPrimeChoice n) ∧ largestPrimeChoice n ∣ n := by
  have hne : (primaryPrimeFactors n).Nonempty := by
    by_contra hempty
    have hchoice : largestPrimeChoice n = 1 := by
      simp only [largestPrimeChoice,dite_eq_right hempty]
    have hone : geometricPrimeBin ρ B (1 : Eisenstein) = geometricBinCount ρ B := by
      simp only [geometricPrimeBin,norm_one_eq,Real.log_one,zero_div,Nat.floor_zero,Nat.sub_zero]
    rw [hchoice,hone] at hbin
    omega
  exact primaryPrimeFactor_spec hn (largestPrimeChoice_spec hne).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedEmptyTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! With no distinguished prime coordinates, the largest prime can only
occur in the selected divisor. This removes an artificial nonempty-tuple
restriction from the stopped-coefficient sequence estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι]

theorem angular_stopped_distinguished_empty (ℓ : ℤ) (B ρ a b w z u : ℝ)
    {j : ℕ} (hj : j < geometricBinCount ρ B) (j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (W : ι → ℝ → ℂ)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D,
      stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
          (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)) = 0 := by
  rw [angular_stoppedBeta_distinguished_original_tuple ℓ]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro f hf
  simp only [Finset.prod_of_isEmpty,one_mul]
  split_ifs with hdiv htest
  · have hp := largestPrimeChoice_prime_of_bin hj (hD d hd) htest.2.2.2
    exact (hp.1.2.not_isUnit (isUnit_of_dvd_one hdiv)).elim
  · rfl
  · rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedAllTuples
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished-role estimate for every finite tuple, including
zero distinguished primes. The empty case is an exact vanishing identity. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stoppedBeta_distinguished_log_saving_all_oai (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E F C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u V : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      0 ≤ b → b ≤ X^C → X^ξ ≤ z → 0 ≤ V →
      |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  rcases isEmpty_or_nonempty ι with he | hn
  · have := he
    refine ⟨1,zero_lt_one,?_⟩
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    intro B ρ a b z u V j _hρ _hρ₂ hj _hPlong hb _hbX _hwz _hV _hu _hVF
      W D₀ _hW _hWi _hWd hD₀ v e _hv _hnc _hNv _he _heX j₀ k h Z Q early
    rw [angular_stopped_distinguished_empty ℓ B ρ a b (X^ξ) z u hj j₀ k h Z Q early W D₀ hD₀ v e,
      norm_zero,one_mul]
    exact div_nonneg hb (Real.rpow_nonneg (Real.log_nonneg hX.le) _)
  · have := hn
    exact angular_stoppedBeta_distinguished_log_saving m hEF ℓ hℓ hA hD hH hF hξ hgap

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all_oai.{u_1} := @OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all_oai.{u_1}
