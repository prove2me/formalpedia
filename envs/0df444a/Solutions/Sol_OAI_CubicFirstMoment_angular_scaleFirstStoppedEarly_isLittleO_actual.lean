-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:10:49.06405+00:00
-- url     : https://prove2.me/submissions/e4cf136c-d66e-4bae-b096-030c75ddca14
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015
import Definitions.Def_OAIQ096A016
import Theorems.Thm_OAI_CubicFirstMoment_angular_stopped_product_bilinear_log_saving_actual

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeJoin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primaryPrime_product_squarefree (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) : Squarefree (∏ p ∈ U, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact isRelPrime_iff_isCoprime.mpr (primaryPrimes_isCoprime (hU p hp) (hU q hq) hpq)
  · intro p hp
    exact (hU p hp).2.squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticUniformWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform support, size and far-left transform bounds from the actual
logarithmic derivative hypotheses on the weight family. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma UniformLogWeights.upper_support {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∀ i x, Real.exp h.radius < x → W i x = 0 := by
  intro i x hx
  by_contra hn
  have hxp : 0 < x := (Real.exp_pos _).trans hx
  have hu : -Real.log x ∈ tsupport (fun u : ℝ => W i (Real.exp (-u))) := by
    apply subset_tsupport
    change W i (Real.exp (-(-Real.log x))) ≠ 0
    simpa only [neg_neg,Real.exp_log hxp] using hn
  have hb := h.support_bound i (-Real.log x) hu
  have hl : Real.log x ≤ h.radius := by
    rw [abs_neg] at hb
    exact (le_abs_self _).trans hb
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hxp] at he
  exact (not_lt_of_ge he) hx

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLatticeModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual squarefree angular model in the low Type-I argument.
Its norm factor is absorbed into the test function, and its cancellation
is obtained from the proved primary-lattice estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealMoebius_sq_complex (u : Eisenstein) :
    (idealMoebius u:ℂ)^2 = if Squarefree u then 1 else 0 := by
  exact_mod_cast idealMoebius_sq u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedActualRange
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordinary stopped range lies strictly inside the stronger
length range needed for the full Gauss Mellin complement. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_stopped_actual_range (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ A b : ℝ,
      X/16 ≤ A*b → A*b ≤ 16*X →
      X^(7/20:ℝ) ≤ b → b ≤ X^(39/100:ℝ) →
      2*b^(3/2:ℝ) ≤ A ∧ A ≤ b^2/(Real.log X)^G := by
  have hlogsave := (isLittleO_log_rpow_rpow_atTop (G:ℝ)
    (by norm_num : (0:ℝ) < 1/20)).def (by norm_num : (0:ℝ) < 1/16)
  filter_upwards [eventually_gt_atTop (1:ℝ),hlogsave,
    eventually_const_mul_rpow_le (by norm_num : (39/40:ℝ) < 1) 32]
    with X hX hlogsave hpower
  intro A b hlo hhi hblo hbhi
  have hXp : 0 < X := zero_lt_one.trans hX
  have hbp : 0 < b := (Real.rpow_pos_of_pos hXp _).trans_le hblo
  have hL : 0 < Real.log X := Real.log_pos hX
  have hlower : 2*b^(3/2:ℝ) ≤ A := by
    have hbpow := Real.rpow_le_rpow hbp.le hbhi (by norm_num : (0:ℝ) ≤ 5/2)
    rw [←Real.rpow_mul hXp.le] at hbpow
    norm_num at hbpow
    have hbsmall : 32*b^(5/2:ℝ) ≤ X :=
      (mul_le_mul_of_nonneg_left hbpow (by norm_num)).trans (by simpa only [Real.rpow_one] using hpower)
    have he : b^(3/2:ℝ)*b = b^(5/2:ℝ) := by
      calc
        _ = b^(3/2:ℝ)*b^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hbp]; norm_num
    apply (mul_le_mul_iff_left₀ hbp).mp
    rw [mul_assoc,he]
    exact (show 2*b^(5/2:ℝ) ≤ X/16 by linarith only [hbsmall]).trans hlo
  have hlogbound : (Real.log X)^G ≤ (1/16:ℝ)*X^(1/20:ℝ) := by
    simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg hL.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hXp.le _)] using hlogsave
  have hbcube : X^(21/20:ℝ) ≤ b^3 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hblo 3
    rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le] at hh
    norm_num at hh
    exact hh
  have hmul : (A*b)*(Real.log X)^G ≤ b^3 := by
    calc
      _ ≤ (16*X)*(Real.log X)^G := mul_le_mul_of_nonneg_right hhi (pow_nonneg hL.le _)
      _ ≤ (16*X)*((1/16:ℝ)*X^(1/20:ℝ)) :=
        mul_le_mul_of_nonneg_left hlogbound (by positivity)
      _ = X^(21/20:ℝ) := by
        have he : X*X^(1/20:ℝ) = X^(21/20:ℝ) := by
          nth_rw 1 [←Real.rpow_one X]
          rw [←Real.rpow_add hXp]
          norm_num
        nlinarith [he]
      _ ≤ _ := hbcube
  refine ⟨hlower,(le_div_iff₀ (pow_pos hL G)).mpr ?_⟩
  apply (mul_le_mul_iff_left₀ hbp).mp
  nlinarith

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothPartitionCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete truncation and subpower cost for the smooth norm partition. -/
noncomputable section
namespace CubicFirstMoment

theorem normPartitionCount_log_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 1 ≤ B →
      (normPartitionCount B : ℝ) ≤ K*(1+Real.log B) := by
  let r := Real.log (4/3:ℝ)
  have hr : 0 < r := Real.log_pos (by norm_num)
  let a := 1+Real.log 2/r
  let b := 1/r
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨a+b,by linarith,?_⟩
  intro B hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hn := (Nat.ceil_lt_add_one
    (div_nonneg (Real.log_nonneg (by linarith : 1 ≤ 2*B)) hr.le)).le
  change (normPartitionCount B : ℝ) ≤ _ at hn
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith : B ≠ 0),add_div] at hn
  have he : Real.log 2/r+Real.log B/r+1 = a+b*Real.log B := by dsimp [a,b]; ring
  apply hn.trans
  rw [he]
  nlinarith [mul_nonneg ha hlog]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual prime-power convolution coefficients: bounded prime support absorbs
all tuple multiplicities in an arbitrarily small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_eq_zero_of_not_mem (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {b : Eisenstein}
    (hb : b ∉ orderedConvolutionSupport S) : orderedConvolution S w b = 0 := by
  unfold orderedConvolution
  apply Finset.sum_eq_zero
  intro f hf
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  exact False.elim (hb (Finset.mem_image.mpr ⟨f,hfs,hfb⟩))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit absorption of the retained norm-dyad count and arbitrarily
small arithmetic losses in a fixed polynomial scale range. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_dyad_count_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ) ≤ C*(1+Real.log J) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C := 1+Real.log 3/Real.log 2+1/Real.log 2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J hJ
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hfloor : (1:ℕ) ≤ ⌊3*J⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    norm_num
    linarith
  have hfloorpos : (0:ℝ) < (⌊3*J⌋₊:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor)
  have hlog := Real.log_le_log hfloorpos (Nat.floor_le (by positivity : 0 ≤ 3*J))
  have hn := Real.natLog_le_logb ⌊3*J⌋₊ 2
  simp only [Real.logb,Nat.cast_ofNat] at hn
  have hjlog := Real.log_nonneg hJ
  have hh : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ) ≤
      (Real.log 3+Real.log J)/Real.log 2 := by
    apply hn.trans
    apply (div_le_div_iff_of_pos_right h2).mpr
    simpa only [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hJp.ne'] using hlog
  rw [Nat.cast_add,Nat.cast_one]
  have hhp : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ)+1 ≤
      (Real.log 3+Real.log J)/Real.log 2+1 := by linarith only [hh]
  apply hhp.trans
  dsimp [C]
  have hx := mul_nonneg (show 0 ≤ 1+Real.log 3/Real.log 2 by positivity) hjlog
  simp only [div_eq_mul_inv] at *
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDyadPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp dyads with the strict lower endpoint used by stopped rows.
The partition is finite and its count depends only on the norm envelope. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedNormDyadLength_pos (j : ℕ) : 0 < stoppedNormDyadLength j := by
  unfold stoppedNormDyadLength
  positivity

lemma stoppedNormDyad_bounds {S : Finset Eisenstein} {j : ℕ} {n : Eisenstein}
    (hn : n ∈ stoppedNormDyad S j) (hnorm : 2 ≤ norm n) :
    stoppedNormDyadLength j/2 < norm n ∧ norm n ≤ stoppedNormDyadLength j := by
  have hN : 2 ≤ normNat n := by exact_mod_cast (show (2:ℝ) ≤ (normNat n:ℝ) by
    simpa only [normNat_cast] using hnorm)
  have hne : normNat n-1 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 2 hne
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (normNat n-1)
  have hj := (Finset.mem_filter.mp hn).2
  change Nat.log 2 (normNat n-1) = j at hj
  rw [hj] at hlo hhi
  have hl : (2:ℕ)^j < normNat n := by omega
  have hu : normNat n ≤ (2:ℕ)^(j+1) := by omega
  have hlr : (2:ℝ)^j < norm n := by
    rw [←normNat_cast]
    exact_mod_cast hl
  have hur : norm n ≤ (2:ℝ)^(j+1) := by
    rw [←normNat_cast]
    exact_mod_cast hu
  unfold stoppedNormDyadLength
  rw [pow_succ]
  constructor
  · nlinarith
  · simpa only [pow_succ] using hur

lemma stoppedNormDyad_outer_bounds {S : Finset Eisenstein} {j : ℕ} {n : Eisenstein}
    (hn : n ∈ stoppedNormDyad S j) (hp : primary n) :
    stoppedNormDyadLength j/2 ≤ norm n ∧ norm n ≤ stoppedNormDyadLength j := by
  by_cases htwo : 2 ≤ norm n
  · have hh := stoppedNormDyad_bounds hn htwo
    exact ⟨hh.1.le,hh.2⟩
  · have hone : 1 ≤ norm n := one_le_norm (primary_ne_zero hp)
    have hN : normNat n = 1 := by
      have hl : 1 ≤ normNat n := by exact_mod_cast (show (1:ℝ) ≤ (normNat n:ℝ) by
        simpa only [normNat_cast] using hone)
      have hu : normNat n < 2 := by exact_mod_cast (show (normNat n:ℝ) < 2 by
        simpa only [normNat_cast] using lt_of_not_ge htwo)
      omega
    have hj : j = 0 := by
      have he := (Finset.mem_filter.mp hn).2
      simpa only [stoppedNormDyadIndex,hN,Nat.sub_self,Nat.log_zero_right] using he.symm
    subst j
    simp only [stoppedNormDyadLength,zero_add,pow_one,div_self (by norm_num : (2:ℝ) ≠ 0)]
    rw [←normNat_cast,hN]
    norm_num

lemma stoppedNormDyad_partition (S : Finset Eisenstein) (f : Eisenstein → ℂ) :
    (∑ n ∈ S, f n) = ∑ j ∈ S.image stoppedNormDyadIndex,
      ∑ n ∈ stoppedNormDyad S j, f n := by
  unfold stoppedNormDyad
  exact (Finset.sum_fiberwise_of_maps_to (s := S)
    (t := S.image stoppedNormDyadIndex) (g := stoppedNormDyadIndex)
    (fun n hn => Finset.mem_image_of_mem _ hn) f).symm

lemma stoppedNormDyad_count (S : Finset Eisenstein) {Y : ℝ}
    (hS : ∀ n ∈ S, norm n ≤ Y) :
    (S.image stoppedNormDyadIndex).card ≤ Nat.log 2 ⌊Y⌋₊+1 := by
  apply le_trans (Finset.card_le_card (show S.image stoppedNormDyadIndex ⊆
    Finset.range (Nat.log 2 ⌊Y⌋₊+1) from ?_)) (by rw [Finset.card_range])
  intro j hj
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  apply Nat.log_mono_right
  exact (Nat.sub_le _ _).trans (Nat.le_floor (by simpa only [normNat_cast] using hS n hn))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primaryFactorRemainder_spec {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    primary (primaryFactorRemainder n s) ∧ Squarefree (primaryFactorRemainder n s) ∧
      (∏ p ∈ s, p)*primaryFactorRemainder n s = n := by
  have hp : ∀ p ∈ primaryPrimeFactors n \ s, primaryPrime p :=
    fun p h => (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp h).1).1
  refine ⟨primary_finset_prod _ _ (fun p h => (hp p h).1),
    primaryPrime_product_squarefree _ hp,?_⟩
  rw [primaryFactorRemainder,mul_comm,Finset.prod_sdiff hsub,primaryPrimeFactors_prod hn hs]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBinGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primary_prime_subset_norm_le {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    norm (∏ p ∈ s, p) ≤ norm n := by
  have he := (primaryFactorRemainder_spec hn hs hsub).2.2
  exact norm_le_of_dvd_nonzero (primary_ne_zero hn) ⟨primaryFactorRemainder n s,he.symm⟩

lemma primary_prime_subset_two_pow_le {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    (2:ℝ)^s.card ≤ norm n := by
  calc
    _ = ∏ _p ∈ s, (2:ℝ) := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ s, norm p := Finset.prod_le_prod (fun _ _ => by norm_num)
      (fun p hp => primaryPrime_norm_ge_two (primaryPrimeFactor_spec hn (hsub hp)).1)
    _ = norm (∏ p ∈ s, p) := (norm_finset_prod _ _).symm
    _ ≤ norm n := primary_prime_subset_norm_le hn hs hsub

lemma primeSurrogate_norm_bounds (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (ell : ℕ → ℝ) {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (hcell : ∀ p ∈ s, 0 ≤ ell (b p) ∧ ell (b p) ≤ norm p ∧ norm p ≤ ρ*ell (b p)) :
    primeSurrogate s b ell ≤ norm (∏ p ∈ s, p) ∧
      norm (∏ p ∈ s, p) ≤ ρ^s.card*primeSurrogate s b ell := by
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod (fun p hp => (hcell p hp).1) (fun p hp => (hcell p hp).2.1)
  · calc
      _ ≤ ∏ p ∈ s, ρ*ell (b p) :=
        Finset.prod_le_prod (fun p _ => norm_nonneg p) (fun p hp => (hcell p hp).2.2)
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]; rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeBins
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem geometricBinCount_log_bound {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 1 ≤ B →
      (geometricBinCount ρ B:ℝ) ≤ K*(1+Real.log B) := by
  let K : ℝ := 1+(Real.log ρ)⁻¹
  have hr : 0 < Real.log ρ := Real.log_pos hρ
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro B hB
  have hl : 0 ≤ Real.log B := Real.log_nonneg hB
  have hi : 0 < (Real.log ρ)⁻¹ := inv_pos.mpr hr
  have h := (Nat.ceil_lt_add_one (div_nonneg hl hr.le)).le
  change (geometricBinCount ρ B:ℝ) ≤ _ at h
  apply h.trans
  dsimp [K]
  rw [div_eq_mul_inv]
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseStoppingLabels
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual final-bin and two-occupancy index set in the stopping
construction has logarithmic size. No complete occupancy vector occurs. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

attribute [local instance] Classical.propDecidable

lemma stoppingFactorLimit_bound {X : ℝ} (hX : 1 ≤ X) :
    (stoppingFactorLimit X:ℝ) ≤ (Real.log 2)⁻¹*Real.log X+1 := by
  have h := (Nat.ceil_lt_add_one
    (div_nonneg (Real.log_nonneg hX) (Real.log_pos (by norm_num : (1:ℝ) < 2)).le)).le
  simpa only [stoppingFactorLimit,div_eq_mul_inv,mul_comm] using h

lemma stoppingLabelBox_card (ρ X : ℝ) :
    (stoppingLabelBox ρ X).card ≤ geometricBinCount ρ X*(stoppingFactorLimit X+1)^2 := by
  unfold stoppingLabelBox
  simpa only [Finset.product_eq_sprod,Finset.card_product,Finset.card_range,pow_two] using
    (Finset.card_filter_le
      ((Finset.range (geometricBinCount ρ X)).product
        ((Finset.range (stoppingFactorLimit X+1)).product
          (Finset.range (stoppingFactorLimit X+1))))
      (fun t : ℕ × ℕ × ℕ => 1 ≤ t.2.1))

lemma stopping_scalar_norm_le_one (k l : ℕ) :
    ‖((Nat.choose (k+l) k:ℂ)⁻¹)‖ ≤ 1 := by
  have hp : 0 < Nat.choose (k+l) k := Nat.choose_pos (by omega)
  have hc : (1:ℝ) ≤ Nat.choose (k+l) k := by exact_mod_cast hp
  rw [norm_inv,Complex.norm_natCast]
  exact inv_le_one_of_one_le₀ hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted finite-sum forms of the exact largest-prime decomposition,
ready for the actual norm twist and cubic character. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPairSupport_primary (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    {n : Eisenstein} (hn : n ∈ primaryPairSupport R D) : primary n := by
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
  exact primary_mul (hR _ hr) (hD _ hd)

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeightBounds
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The height weight in the truncated Mellin integral

The interval transform has the expected `1/(1+|ξ|)` bound, including
at frequency zero. The cutoff and the scaling phase have norm at most one.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace CubicFirstMoment

lemma norm_dyadicFourierMultiplier_le_log (ξ : ℝ) :
    ‖dyadicFourierMultiplier ξ‖ ≤ Real.log 2 := by
  unfold dyadicFourierMultiplier
  rw [fourier_intervalStep_eq_integral (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.log 2) (C := (1 : ℝ))
    (f := fun x => Complex.exp ((-2*Real.pi*x*ξ : ℝ)*Complex.I))
    (fun x _ => (Complex.norm_exp_ofReal_mul_I _).le)
  simpa only [sub_zero, abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)),
    one_mul] using h

lemma norm_frequencyCutoff_le_one (ξ : ℝ) : ‖frequencyCutoff ξ‖ ≤ 1 := by
  rw [frequencyCutoff_apply,Complex.norm_real,Real.norm_of_nonneg frequencyBump.nonneg]
  exact frequencyBump.le_one

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowHeightIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-height weight has a direct polynomial-logarithmic cost.
This transfers the uniform corrected Type-I/II estimates to its integral. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cutoffHeightMultiplier_norm_le_log (H t : ℝ) :
    ‖cutoffHeightMultiplier H t‖ ≤ Real.log 2 := by
  change ‖frequencyCutoff ((t/(2*Real.pi))/H)*
    dyadicFourierMultiplier (t/(2*Real.pi))‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (_root_.norm_nonneg _)
    (norm_frequencyCutoff_le_one _)).trans (norm_dyadicFourierMultiplier_le_log _)

lemma lowHeightWeight_norm_le (H T t : ℝ) :
    ‖lowHeightWeight H T t‖ ≤ Real.log 2 := by
  rw [lowHeightWeight,norm_mul]
  apply (mul_le_of_le_one_right (_root_.norm_nonneg _) ?_).trans
    (cutoffHeightMultiplier_norm_le_log H t)
  simpa only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg heightPartitionBump.nonneg] using
    (heightPartitionBump.le_one (x := t/T))

lemma lowHeightWeight_zero (H : ℝ) {T t : ℝ} (hT : 0 < T)
    (ht : t ∉ Icc (-(4/3)*T) ((4/3)*T)) : lowHeightWeight H T t = 0 := by
  have hh : 4/3 ≤ |t/T| := by
    rw [abs_div,abs_of_pos hT]
    apply (le_div_iff₀ hT).mpr
    have hn : ¬(-(4/3)*T ≤ t ∧ t ≤ (4/3)*T) := ht
    rw [le_abs]
    by_cases hp : t ≤ (4/3)*T
    · have hl : t < -(4/3)*T := lt_of_not_ge (fun hl => hn ⟨hl,hp⟩)
      exact Or.inr (by linarith)
    · exact Or.inl (le_of_lt (lt_of_not_ge hp))
  rw [lowHeightWeight,heightPartitionBump_zero hh,Complex.ofReal_zero,mul_zero]

theorem lowHeightWeight_integral_bound (H : ℝ) {T B : ℝ}
    (hT : 0 < T) (_hB : 0 ≤ B) (f : ℝ → ℂ)
    (hf : ∀ t ∈ Icc (-(4/3)*T) ((4/3)*T), ‖f t‖ ≤ B) :
    ‖∫ t : ℝ, lowHeightWeight H T t*f t‖ ≤ (8/3)*Real.log 2*T*B := by
  let S : Set ℝ := Icc (-(4/3)*T) ((4/3)*T)
  let b : ℝ := Real.log 2*B
  have hi : Integrable (S.indicator (fun _ => b)) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hb : ‖∫ t : ℝ, lowHeightWeight H T t*f t‖ ≤
      ∫ t : ℝ, S.indicator (fun _ => b) t := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with t
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht,norm_mul]
      exact mul_le_mul (lowHeightWeight_norm_le H T t) (hf t ht)
        (_root_.norm_nonneg _) (Real.log_nonneg (by norm_num))
    · rw [indicator_of_notMem ht,lowHeightWeight_zero H hT ht,zero_mul,norm_zero]
  apply hb.trans_eq
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),intervalIntegral.integral_const]
  dsimp [b]
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

lemma dispersionCutoff_positive_support (R : ℝ) :
    tsupport (fun x => (dispersionCutoff R x:ℂ)) ⊆ Ioi 0 := by
  intro x hx
  have := (dispersionCutoff_tsupport R hx).1
  change 0 < x
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLowHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a uniform low-height arithmetic bound to the actual
low-height term of the sharp prime comparison. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma lowHeightWeight_integrable {H : ℝ} (hH : 0 < H) (T : ℝ) :
    Integrable (lowHeightWeight H T) := by
  apply (cutoffHeightMultiplier_integrable hH).mul_bdd (c := 1)
  · exact (Complex.continuous_ofReal.comp
      (heightPartitionBump.continuous.comp (continuous_id.div_const T))).aestronglyMeasurable
  · filter_upwards with t
    simpa only [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg heightPartitionBump.nonneg] using
      (heightPartitionBump.le_one (x := t/T))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove only the proved zero terms when the detector's finite
squarefree envelope is put into a Type-I row. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma centeredGauss_zero_of_not_squarefree {n : Eisenstein} (hn : primary n)
    (hs : ¬Squarefree n) : centeredGauss n = 0 := by
  rw [centeredGauss,gauss_eq_zero_of_not_squarefree hn hs,
    idealMoebius_sq_complex,ite_eq_right hs]
  ring

lemma productCenteredKernel_envelope (ℓ : ℤ) (W : ℝ → ℂ) {B X : ℝ}
    (hX : 0 < X) (hW : ∀ x : ℝ, B < x → W x = 0)
    (t : ℝ) {n : Eisenstein} (hn : primary n) :
    (if n ∈ squarefreeProductEnvelope (B*X) then productCenteredKernel ℓ W X t n else 0) =
      productCenteredKernel ℓ W X t n := by
  by_cases hs : Squarefree n
  · by_cases hsize : norm n ≤ B*X
    · have hm : n ∈ squarefreeProductEnvelope (B*X) :=
        Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hn,hsize⟩,hs⟩
      rw [ite_eq_left hm]
    · have hx : B < norm n/X := (lt_div_iff₀ hX).mpr (lt_of_not_ge hsize)
      simp only [productCenteredKernel,hW _ hx,mul_zero,ite_self]
  · simp only [productCenteredKernel,centeredGauss_zero_of_not_squarefree hn hs,
      mul_zero,zero_mul,ite_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The product-envelope Type-I integral equals the literal finite
height-Fourier kernel used in the detector decomposition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma centeredHeightKernel_envelope (ℓ : ℤ) (W : ℝ → ℂ) {B X : ℝ}
    (hX : 0 < X) (hW : ∀ x : ℝ, B < x → W x = 0)
    (H T X₀ : ℝ) {n : Eisenstein} (hn : primary n) :
    (if n ∈ squarefreeProductEnvelope (B*X) then centeredHeightKernel ℓ W H T X X₀ n else 0) =
      centeredHeightKernel ℓ W H T X X₀ n := by
  have he := congrArg (fun z : ℂ => z*heightFourierIntegral (lowHeightWeight H T)
    (Real.log (norm n)-Real.log X₀)) (productCenteredKernel_envelope ℓ W hX hW 0 hn)
  simpa only [ite_mul,zero_mul,productCenteredKernel,normTwist,zero_mul,
    Complex.ofReal_zero,Complex.exp_zero,mul_one,centeredHeightKernel] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeModelLogTail
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The model is already negligible above a sufficiently large power
of the logarithm. This leaves the genuinely low-height corrected sum. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_log_saving_isLittleO :
    (fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) =o[atTop] firstMomentScale := by
  have hL : Tendsto (fun X : ℝ => 1+Real.log X) atTop atTop :=
    tendsto_const_nhds.add_atTop Real.tendsto_log_atTop
  have hi := tendsto_inv_atTop_zero.comp hL
  have hconst : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hh := (hconst.sub hi).mul (hi.pow 2)
  simp only [sub_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero] at hh
  apply Asymptotics.isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    have hp : 0 < firstMomentScale X := div_pos
      (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) (Real.log_pos hX)
    exact fun hz => (hp.ne' hz).elim
  · apply hh.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    have hp : 0 < X := zero_lt_one.trans hX
    have hl : 0 < Real.log X := Real.log_pos hX
    unfold firstMomentScale
    simp only [Function.comp_apply]
    field_simp [(Real.rpow_pos_of_pos hp (5/6:ℝ)).ne',hl.ne',
      show 1+Real.log X ≠ 0 by positivity]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductEnvelope
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth product envelope equals one on the full sharp dyadic
interval. Thus the exact prime cutoff can be retained in the height integral
while every factorized row has a smooth product weight. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma primeProductEnvelope_zero {x : ℝ} (hx : 3 ≤ x) : primeProductEnvelope x = 0 := by
  have h : primeProductBump x = 0 := by
    apply primeProductBump.zero_of_le_dist
    change 1 ≤ |x-3/2|
    exact (by linarith : (1:ℝ) ≤ x-3/2).trans (le_abs_self _)
  simp only [primeProductEnvelope,h,Complex.ofReal_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductDetector
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the manuscript's exact prime detector to the actual central
integral kernel. The support is a concrete subset of the primary lattice,
with both norm endpoints enforced before the detector is invoked. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeProductEnvelope_zero_lower {x : ℝ} (hx : x ≤ 1/2) :
    primeProductEnvelope x = 0 := by
  have h : primeProductBump x = 0 := by
    apply primeProductBump.zero_of_le_dist
    change 1 ≤ |x-3/2|
    exact (by linarith : (1:ℝ) ≤ -(x-3/2)).trans (neg_le_abs _)
  simp only [primeProductEnvelope,h,Complex.ofReal_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CentralProductSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth product kernel permits the exact detector support to be
replaced by its full squarefree envelope. No nonzero term is removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma centralProductEnvelope_spec {X : ℝ} {n : Eisenstein}
    (hn : n ∈ centralProductEnvelope X) :
    primary n ∧ Squarefree n ∧ norm n ≤ Real.exp primeProductWeights.radius*X := by
  obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
  exact ⟨(mem_primaryElementBall.mp hn).1,hs,(mem_primaryElementBall.mp hn).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedKernelRange
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Norm geometry of the actual stopped kernel, before any analytic
estimate. Sharp side dyads imply the strengthened bilinear length range. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma centeredHeightKernel_norm_range (ℓ : ℤ) (H T : ℝ) {X : ℝ}
    (hX : 0 < X) {n : Eisenstein}
    (hne : centeredHeightKernel ℓ primeProductEnvelope H T X X n ≠ 0) :
    X/2 < norm n ∧ norm n < 3*X := by
  have hW : primeProductEnvelope (norm n/X) ≠ 0 := by
    intro hz
    apply hne
    simp only [centeredHeightKernel,hz,mul_zero,zero_mul]
  constructor
  · by_contra hn
    apply hW
    apply primeProductEnvelope_zero_lower
    exact (div_le_iff₀ hX).mpr (by linarith)
  · by_contra hn
    apply hW
    apply primeProductEnvelope_zero
    exact (le_div_iff₀ hX).mpr (by linarith)

lemma stopped_dyad_product_range {X A B : ℝ} {a b : Eisenstein}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : A ≤ norm a ∧ norm a ≤ 2*A)
    (hb : B/2 ≤ norm b ∧ norm b ≤ B)
    (hprod : X/2 ≤ norm (a*b) ∧ norm (a*b) ≤ 3*X) :
    X/4 ≤ A*B ∧ A*B ≤ 6*X := by
  rw [norm_mul_eq] at hprod
  have hu := mul_le_mul ha.2 hb.2 (norm_nonneg _) (by positivity : 0 ≤ 2*A)
  have hl := mul_le_mul ha.1 hb.1 (by positivity : 0 ≤ B/2) (norm_nonneg _)
  constructor <;> nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMatrixDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent sharp side dyads for the stopped matrices. The
squarefree product envelope supplies the side support; no coprimality
restriction or boundary contribution is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma centralProduct_factor_support {X : ℝ} {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hab : a*b ∈ centralProductEnvelope X) :
    (Squarefree a ∧ norm a ≤ Real.exp primeProductWeights.radius*X) ∧
      (Squarefree b ∧ norm b ≤ Real.exp primeProductWeights.radius*X) := by
  have hs := centralProductEnvelope_spec hab
  have hn := primary_ne_zero (primary_mul ha hb)
  exact ⟨⟨hs.2.1.of_mul_left,
    (norm_le_of_dvd hn (dvd_mul_right a b)).trans hs.2.2⟩,
    ⟨hs.2.1.of_mul_right,(norm_le_of_dvd hn (dvd_mul_left b a)).trans hs.2.2⟩⟩

lemma stopped_matrix_side_support (P Q : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hQ : ∀ b ∈ Q, primary b)
    (α β K : Eisenstein → ℂ) (X : ℝ) :
    (∑ a ∈ P, ∑ b ∈ Q, α a*β b*
      (if a*b ∈ centralProductEnvelope X then K (a*b) else 0)) =
    ∑ a ∈ stoppedFactorSupport P X, ∑ b ∈ stoppedFactorSupport Q X,
      α a*β b*(if a*b ∈ centralProductEnvelope X then K (a*b) else 0) := by
  unfold stoppedFactorSupport
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hsa : Squarefree a ∧ norm a ≤ Real.exp primeProductWeights.radius*X
  · rw [ite_eq_left hsa]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hsb : Squarefree b ∧ norm b ≤ Real.exp primeProductWeights.radius*X
    · rw [ite_eq_left hsb]
    · have hz : a*b ∉ centralProductEnvelope X :=
        fun hab => hsb (centralProduct_factor_support (hP a ha) (hQ b hb) hab).2
      simp only [ite_eq_right hsb,ite_eq_right hz,mul_zero]
  · rw [ite_eq_right hsa]
    apply Finset.sum_eq_zero
    intro b hb
    have hz : a*b ∉ centralProductEnvelope X :=
      fun hab => hsa (centralProduct_factor_support (hP a ha) (hQ b hb) hab).1
    simp only [ite_eq_right hz,mul_zero]

lemma finite_matrix_stopped_dyads (P Q : Finset Eisenstein)
    (F : Eisenstein → Eisenstein → ℂ) :
    (∑ a ∈ P, ∑ b ∈ Q, F a b) =
      ∑ j ∈ P.image stoppedNormDyadIndex, ∑ k ∈ Q.image stoppedNormDyadIndex,
        ∑ a ∈ stoppedNormDyad P j, ∑ b ∈ stoppedNormDyad Q k, F a b := by
  rw [stoppedNormDyad_partition P]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ a ∈ stoppedNormDyad P j, ∑ k ∈ Q.image stoppedNormDyadIndex,
        ∑ b ∈ stoppedNormDyad Q k, F a b := by
      apply Finset.sum_congr rfl
      intro a _
      exact stoppedNormDyad_partition Q (F a)
    _ = _ := Finset.sum_comm

lemma stopped_matrix_dyadic (P Q : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hQ : ∀ b ∈ Q, primary b)
    (α β K : Eisenstein → ℂ) (X : ℝ) :
    (∑ a ∈ P, ∑ b ∈ Q, α a*β b*
      (if a*b ∈ centralProductEnvelope X then K (a*b) else 0)) =
      ∑ j ∈ (stoppedFactorSupport P X).image stoppedNormDyadIndex,
        ∑ k ∈ (stoppedFactorSupport Q X).image stoppedNormDyadIndex,
          ∑ a ∈ stoppedNormDyad (stoppedFactorSupport P X) j,
            ∑ b ∈ stoppedNormDyad (stoppedFactorSupport Q X) k,
              α a*β b*(if a*b ∈ centralProductEnvelope X then K (a*b) else 0) := by
  rw [stopped_matrix_side_support P Q hP hQ α β K X]
  exact finite_matrix_stopped_dyads _ _ _

lemma stoppedFactorSupport_log_count :
    ∃ D : ℝ, 0 < D ∧ ∀ (X : ℝ), 1 ≤ X → ∀ P : Finset Eisenstein,
      (((stoppedFactorSupport P X).image stoppedNormDyadIndex).card:ℝ) ≤
        D*(1+Real.log X) := by
  obtain ⟨C,hC,hcount⟩ := metaplectic_dyad_count_log_bound
  let R := primeProductWeights.radius
  refine ⟨C*(1+R),by dsimp [R]; positivity [primeProductWeights.radius_nonneg],?_⟩
  intro X hX P
  have hF : 1 ≤ Real.exp R*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  have hc := stoppedNormDyad_count (stoppedFactorSupport P X)
    (fun n hn => (Finset.mem_filter.mp hn).2.2)
  have hm : Nat.log 2 ⌊Real.exp R*X⌋₊+1 ≤ Nat.log 2 ⌊3*(Real.exp R*X)⌋₊+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono (by nlinarith))) 1
  calc
    _ ≤ ((Nat.log 2 ⌊3*(Real.exp R*X)⌋₊+1:ℕ):ℝ) := Nat.cast_le.mpr (hc.trans hm)
    _ ≤ C*(1+Real.log (Real.exp R*X)) := hcount _ hF
    _ ≤ C*(1+R)*(1+Real.log X) := by
      rw [Real.log_mul (Real.exp_pos _).ne' (zero_lt_one.trans_le hX).ne',Real.log_exp]
      have hR : 0 ≤ R := primeProductWeights.radius_nonneg
      have hL := Real.log_nonneg hX
      calc
        _ ≤ C*((1+R)*(1+Real.log X)) := mul_le_mul_of_nonneg_left
          (by nlinarith [mul_nonneg hR hL]) hC.le
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite tuple norm partition has only a fixed power of the
logarithm many pieces, uniformly in the growing prime envelope. -/
noncomputable section
namespace CubicFirstMoment

theorem largePrimeTuplePartition_count (i j : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℝ, 1 ≤ X →
      (Fintype.card ((Fin i ⊕ Fin j) → Fin
        (normPartitionCount (Real.exp primeProductWeights.radius*X))):ℝ) ≤
        D*(1+Real.log X)^(i+j) := by
  obtain ⟨K,hK,hcount⟩ := normPartitionCount_log_bound
  let R := primeProductWeights.radius
  have hR : 0 ≤ R := primeProductWeights.radius_nonneg
  refine ⟨(K*(1+R))^(i+j),by positivity,?_⟩
  intro X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hBX : 1 ≤ Real.exp R*X := one_le_mul_of_one_le_of_one_le (Real.one_le_exp hR) hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hb := hcount (Real.exp R*X) hBX
  rw [Real.log_mul (Real.exp_pos R).ne' hXp.ne',Real.log_exp] at hb
  have hN : (normPartitionCount (Real.exp R*X):ℝ) ≤ K*(1+R)*(1+Real.log X) := by
    apply hb.trans
    nlinarith [mul_nonneg hR hlogX]
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,Nat.cast_pow]
  change (normPartitionCount (Real.exp R*X):ℝ)^(i+j) ≤ _
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hN (i+j)).trans_eq
  rw [mul_pow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularScaleFirstStoppedDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-angular low-height stopping rows, retaining the original
coefficients, product support, and inverse-binomial factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_distinguishedScaleStoppedRow_dyads (ℓ : ℤ) (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    angular_distinguishedScaleStoppedRow ℓ i ρ ξ Ct H X h early d =
      ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ j ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
            ∑ k ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
              angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h early d q j k := by
  unfold angular_distinguishedScaleStoppedRow
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact stopped_matrix_dyadic _ _
    (fun a ha => primaryPairSupport_primary _ _
      (fun _ hn => (mem_primaryElementBall.mp hn).1)
      (fun _ hn => (mem_primaryElementBall.mp hn).1) ha)
    (fun b hb => primaryPairSupport_primary _ _
      (fun _ hn => (mem_primaryElementBall.mp hn).1)
      (fun _ hn => (mem_primaryElementBall.mp hn).1) hb)
    _ _ _ X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingLabelWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit logarithmic aggregation costs for the actual finite stopping
labels on a fixed dilation of X. The inverse-binomial scalar is retained,
and the bounds apply to every early or late subset of labels. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stoppingLabelBox_card_fixed {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : ℝ, 1 ≤ F →
      ((stoppingLabelBox ρ F).card:ℝ) ≤ K*(1+Real.log F)^3 := by
  obtain ⟨C,hC,hbin⟩ := geometricBinCount_log_bound hρ
  let D : ℝ := (Real.log 2)⁻¹+2
  have hlog2 : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C*D^2,by positivity,?_⟩
  intro F hF
  have hL := Real.log_nonneg hF
  have hf := stoppingFactorLimit_bound hF
  have hfac : ((stoppingFactorLimit F+1:ℕ):ℝ) ≤ D*(1+Real.log F) := by
    simp only [Nat.cast_add,Nat.cast_one]
    dsimp [D]
    nlinarith
  have hcard : ((stoppingLabelBox ρ F).card:ℝ) ≤
      (geometricBinCount ρ F:ℝ)*((stoppingFactorLimit F+1:ℕ):ℝ)^2 := by
    exact_mod_cast stoppingLabelBox_card ρ F
  calc
    _ ≤ (C*(1+Real.log F))*(D*(1+Real.log F))^2 :=
      hcard.trans (mul_le_mul (hbin F hF)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hfac 2) (sq_nonneg _) (by positivity))
    _ = (C*D^2)*(1+Real.log F)^3 := by ring

theorem stoppingLabelBox_card_dilated {ρ c : ℝ} (hρ : 1 < ρ) (hc : 1 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      ((stoppingLabelBox ρ (c*X)).card:ℝ) ≤ K*(1+Real.log X)^3 := by
  obtain ⟨C,hC,hbound⟩ := stoppingLabelBox_card_fixed hρ
  have hclog := Real.log_nonneg hc
  have hcp : 0 < c := zero_lt_one.trans_le hc
  refine ⟨C*(1+Real.log c)^3,by positivity,?_⟩
  intro X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlogX := Real.log_nonneg hX
  have hF : 1 ≤ c*X := one_le_mul_of_one_le_of_one_le hc hX
  have hL : 1+Real.log (c*X) ≤ (1+Real.log c)*(1+Real.log X) := by
    rw [Real.log_mul hcp.ne' hXp.ne']
    nlinarith [mul_nonneg hclog hlogX]
  calc
    _ ≤ C*(1+Real.log (c*X))^3 := hbound _ hF
    _ ≤ C*((1+Real.log c)*(1+Real.log X))^3 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity [Real.log_nonneg hF]) hL 3) hC.le
    _ = (C*(1+Real.log c)^3)*(1+Real.log X)^3 := by ring

/-- One constant covers arbitrary early/late label subsets and every
family of piece bounds. In particular, no sign is discarded from a piece. -/
theorem stopping_label_weighted_sum_dilated {ρ c : ℝ} (hρ : 1 < ρ) (hc : 1 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ I : Finset (ℕ × ℕ × ℕ), I ⊆ stoppingLabelBox ρ (c*X) →
      (I.card:ℝ) ≤ K*(1+Real.log X)^3 ∧
      ∀ (f : (ℕ × ℕ × ℕ) → ℂ) (M : ℝ), 0 ≤ M →
        (∀ q ∈ I, ‖f q‖ ≤ M) →
        ‖∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*f q‖ ≤
          K*(1+Real.log X)^3*M := by
  obtain ⟨K,hK,hcount⟩ := stoppingLabelBox_card_dilated hρ hc
  refine ⟨K,hK,?_⟩
  intro X hX I hI
  have hcard : (I.card:ℝ) ≤ K*(1+Real.log X)^3 :=
    (Nat.cast_le.mpr (Finset.card_le_card hI)).trans (hcount X hX)
  refine ⟨hcard,?_⟩
  intro f M hM hf
  calc
    _ ≤ ∑ q ∈ I, ‖(Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*f q‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ I, M := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_mul (stopping_scalar_norm_le_one q.2.1 q.2.2) (hf q hq)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    _ = (I.card:ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hM

/-- The low distinguished-scale restriction can only lower the number of
norm-partition indices; its exact cutoff need not be relaxed. -/
theorem stopped_norm_partition_subset_count (i : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ I : Finset (Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
        (I.card:ℝ) ≤ D*(1+Real.log X)^i := by
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i 0
  refine ⟨D,hD,?_⟩
  intro X hX I
  have hi : (I.card:ℝ) ≤ (Fintype.card
      (Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))):ℝ) := by
    exact_mod_cast Finset.card_le_univ I
  apply hi.trans
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,Nat.add_zero,Nat.cast_pow]
    using hcount X hX

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedAggregation
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite stopping sums cost only a fixed power of log X. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_double_sum_le_card_sq {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → κ → ℂ) {M : ℝ} (hf : ∀ i ∈ S, ∀ j ∈ T, ‖f i j‖ ≤ M) :
    ‖∑ i ∈ S, ∑ j ∈ T, f i j‖ ≤ (S.card:ℝ)*(T.card:ℝ)*M := by
  calc
    _ ≤ ∑ i ∈ S, ‖∑ j ∈ T, f i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, (T.card:ℝ)*M := by
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      simpa only [Finset.sum_const,nsmul_eq_mul] using
        Finset.sum_le_sum (s := T) (fun j hj => hf i hi j hj)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularScaleFirstStoppedAggregation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-angular low-height stopping rows, retaining the original
coefficients, product support, and inverse-binomial factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_distinguishedScaleStoppedRow_bound (ℓ : ℤ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i Ct : ℕ) (ξ H X : ℝ), 1 ≤ X → ∀ (h : ℕ) (early : Bool)
      (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (M : ℝ), 0 ≤ M →
      (∀ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        ∀ j k : ℕ, ‖angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h early d q j k‖ ≤ M) →
      ‖angular_distinguishedScaleStoppedRow ℓ i ρ ξ Ct H X h early d‖ ≤
        K*(1+Real.log X)^5*M := by
  obtain ⟨D,hD,hcount⟩ := stoppedFactorSupport_log_count
  obtain ⟨C,hC,hlabels⟩ := stopping_label_weighted_sum_dilated hρ
    (Real.one_le_exp primeProductWeights.radius_nonneg)
  refine ⟨C*D^2,by positivity,?_⟩
  intro i Ct ξ H X hX h early d M hM hpiece
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  let I := if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
    (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)
  let J := (distinguishedStoppedSide X).image stoppedNormDyadIndex
  have hI : I ⊆ stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X) := by
    dsimp [I]
    split
    · exact Finset.filter_subset _ _
    · exact Finset.Subset.refl _
  have hJ : (J.card:ℝ) ≤ D*(1+Real.log X) := hcount X hX _
  have hJ0 : 0 ≤ (J.card:ℝ) := Nat.cast_nonneg _
  have hinner (q) (hq : q ∈ I) :
      ‖∑ j ∈ J, ∑ k ∈ J, angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h early d q j k‖ ≤
        D^2*(1+Real.log X)^2*M := by
    apply (norm_double_sum_le_card_sq J J _ (fun j _ k _ => hpiece q hq j k)).trans
    have hs := mul_le_mul hJ hJ hJ0 (by positivity : 0 ≤ D*(1+Real.log X))
    calc
      _ ≤ (D*(1+Real.log X))*(D*(1+Real.log X))*M := mul_le_mul_of_nonneg_right hs hM
      _ = _ := by ring
  rw [angular_distinguishedScaleStoppedRow_dyads]
  have hh := (hlabels X hX I hI).2 _ (D^2*(1+Real.log X)^2*M)
    (by positivity) hinner
  apply hh.trans_eq
  ring

theorem angular_distinguishedScaleStopped_bound (ℓ : ℤ) (i : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ct : ℕ) (ξ H X : ℝ), 1 ≤ X → ∀ (h : ℕ) (early : Bool)
      (M : ℝ), 0 ≤ M →
      (∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ),
        q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)) →
        ∀ j k : ℕ, ‖angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h early d q j k‖ ≤ M) →
      ‖angular_distinguishedScaleStopped ℓ i ρ ξ Ct H X h early‖ ≤
        K*(1+Real.log X)^(i+5)*M := by
  obtain ⟨C,hC,hrow⟩ := angular_distinguishedScaleStoppedRow_bound ℓ hρ
  obtain ⟨D,hD,hcount⟩ := stopped_norm_partition_subset_count i
  refine ⟨D*C,by positivity,?_⟩
  intro Ct ξ H X hX h early M hM hpiece
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  let S := (Finset.univ : Finset (Fin i → Fin
    (normPartitionCount (Real.exp primeProductWeights.radius*X))))
  have hb (d) : ‖(if distinguishedScaleLength d < X^(69/200:ℝ) then
      angular_distinguishedScaleStoppedRow ℓ i ρ ξ Ct H X h early d else 0)‖ ≤
      C*(1+Real.log X)^5*M := by
    split_ifs
    · exact hrow i Ct ξ H X hX h early d M hM (hpiece d)
    · rw [norm_zero]; positivity
  calc
    _ ≤ ∑ d ∈ S, C*(1+Real.log X)^5*M := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun d _ => hb d)
    _ = (S.card:ℝ)*(C*(1+Real.log X)^5*M) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (D*(1+Real.log X)^i)*(C*(1+Real.log X)^5*M) :=
      mul_le_mul_of_nonneg_right (hcount X hX S) (by positivity)
    _ = _ := by rw [pow_add]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormPartitionVariation
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scaled derivative bounds for the actual distinguished norm
partition. Rescaling the prime norm introduces no growing variation cost. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma normPartitionWeight_deriv_zero {x : ℝ} (hx : x ∉ Icc (1:ℝ) 2) :
    deriv normPartitionWeight x = 0 := by
  by_cases hlo : x < 1
  · have he : EqOn normPartitionWeight (fun _ : ℝ => (0:ℂ)) (Iio 1) :=
      fun _ hy => normPartitionWeight_low hy
    simpa only [deriv_const] using he.deriv isOpen_Iio hlo
  · have hhi : 2 < x := by
      rcases not_and_or.mp hx with h | h
      · exact False.elim (h (le_of_not_gt hlo))
      · exact lt_of_not_ge h
    have he : EqOn normPartitionWeight (fun _ : ℝ => (0:ℂ)) (Ioi 2) :=
      fun _ hy => normPartitionWeight_high hy
    simpa only [deriv_const] using he.deriv isOpen_Ioi hhi

theorem normPartitionWeight_radial_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x → ‖deriv normPartitionWeight x‖*x ≤ D := by
  have hd : Continuous (deriv normPartitionWeight) :=
    normPartitionWeight_smooth.continuous_deriv (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((hd.norm.mul continuous_id).continuousOn)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x hx
  by_cases hmem : x ∈ Icc (1:ℝ) 2
  · have h := hD x hmem
    change ‖‖deriv normPartitionWeight x‖*x‖ ≤ D at h
    rw [Real.norm_of_nonneg (mul_nonneg (_root_.norm_nonneg _) hx.le)] at h
    exact h.trans (le_max_left _ _)
  · rw [normPartitionWeight_deriv_zero hmem,norm_zero,zero_mul]
    exact le_max_right _ _

lemma scaledNormPartitionWeight_smooth (c : ℝ) :
    ContDiff ℝ ∞ (scaledNormPartitionWeight c) :=
  normPartitionWeight_smooth.comp (contDiff_const.mul contDiff_id)

lemma scaledNormPartitionWeight_norm (c x : ℝ) : ‖scaledNormPartitionWeight c x‖ ≤ 1 :=
  normPartitionWeight_norm _

theorem scaledNormPartitionWeight_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ c : ℝ, 0 < c → ∀ x : ℝ, 0 < x →
      ‖deriv (scaledNormPartitionWeight c) x‖*x ≤ D := by
  obtain ⟨D,hD,hbound⟩ := normPartitionWeight_radial_deriv_bound
  refine ⟨D,hD,?_⟩
  intro c hc x hx
  have hd := ((normPartitionWeight_smooth.differentiable (by norm_num)).differentiableAt
    (x := c*x)).hasDerivAt.scomp x (hasDerivAt_const_mul c)
  have he : deriv (scaledNormPartitionWeight c) x = c • deriv normPartitionWeight (c*x) := hd.deriv
  rw [he,norm_smul,Real.norm_of_nonneg hc.le]
  calc
    _ = ‖deriv normPartitionWeight (c*x)‖*(c*x) := by ring
    _ ≤ D := hbound _ (mul_pos hc hx)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedStoppingWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished scale coefficients use a single bounded-variation
family at every partition scale, exactly as the stopped estimate requires. -/
noncomputable section
open Filter
open scoped ContDiff
namespace CubicFirstMoment

lemma distinguishedStoppingWeights_at {i N : ℕ} (k : Fin i → Fin N)
    (j : Fin i) (p : Eisenstein) :
    distinguishedStoppingWeights k j (norm p) =
      normPartitionWeight (2*norm p/(4/3:ℝ)^(k j).val) := by
  unfold distinguishedStoppingWeights scaledNormPartitionWeight
  congr 1
  ring

theorem distinguishedStoppingWeights_uniform :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (i N : ℕ) (k : Fin i → Fin N),
      (∀ j x, ‖distinguishedStoppingWeights k j x‖ ≤ 1) ∧
      (∀ j, ContDiff ℝ ∞ (distinguishedStoppingWeights k j)) ∧
      (∀ j x, 0 < x → ‖deriv (distinguishedStoppingWeights k j) x‖*x ≤ V) := by
  obtain ⟨V,hV,hbound⟩ := scaledNormPartitionWeight_deriv_bound
  refine ⟨V,hV,?_⟩
  intro i N k
  exact ⟨fun _ _ => scaledNormPartitionWeight_norm _ _,
    fun _ => scaledNormPartitionWeight_smooth _,
    fun j x hx => hbound _ (by positivity) x hx⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCharacterRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal stopped character sum as a squarefree coefficient row.
The norm phase preserves its energy, and the energy is derived from the
actual distinguished coefficient rather than supplied as a hypothesis. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedIntervalSupport_spec (X a b : ℝ) (e : Eisenstein)
    {n : Eisenstein} (hn : n ∈ stoppedIntervalSupport ι X a b e) :
    primary n ∧ Squarefree n ∧ norm n ≤ b := by
  obtain ⟨hm,hs,_,_,hb⟩ := Finset.mem_filter.mp hn
  have hp := primaryPairSupport_primary _ _
    (fun r hr => orderedPrimarySupport_primary _
      (fun _ _ h => (mem_primeCutoff.mp h).1.1) hr)
    (fun d hd => (mem_primaryElementBall.mp hd).1) hm
  exact ⟨hp,hs,hb⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedRowRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-envelope changes for the actual stopped coefficient.
Every factor in a fibre divides its prescribed product. Thus a bounded
product uses only the smaller prime and divisor cutoffs. The selected-side
predicate is retained verbatim, including any extra restriction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedBeta_selected_congr (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected selected' : Eisenstein → Eisenstein → Prop)
    (b : Eisenstein)
    (hselected : ∀ r ∈ R, ∀ d ∈ D, r*d = b → (selected r d ↔ selected' r d)) :
    stoppedBeta R D v ψ w selected b = stoppedBeta R D v ψ w selected' b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
  obtain ⟨hr,hd⟩ := Finset.mem_product.mp hp
  dsimp only
  rw [propext (hselected p.1 hr p.2 hd he)]

lemma primaryPairFiber_ball_restrict {X F : ℝ} (hXF : X ≤ F)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    primaryPairFiber (primaryElementBall F) (primaryElementBall F) b =
      primaryPairFiber (primaryElementBall X) (primaryElementBall X) b := by
  ext p
  simp only [primaryPairFiber,Finset.mem_filter,Finset.mem_product]
  constructor
  · rintro ⟨⟨hr,hd⟩,he⟩
    have hrb : p.1 ∣ b := ⟨p.2,he.symm⟩
    have hdb : p.2 ∣ b := ⟨p.1,by rw [mul_comm,he]⟩
    exact ⟨⟨mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hr).1,
      (norm_le_of_dvd (primary_ne_zero hb) hrb).trans hbX⟩,
      mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hd).1,
      (norm_le_of_dvd (primary_ne_zero hb) hdb).trans hbX⟩⟩,he⟩
  · rintro ⟨⟨hr,hd⟩,he⟩
    exact ⟨⟨mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hr).1,
      (mem_primaryElementBall.mp hr).2.trans hXF⟩,
      mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hd).1,
      (mem_primaryElementBall.mp hd).2.trans hXF⟩⟩,he⟩

lemma primeTupleFiber_restrict {X F : ℝ} (hXF : X ≤ F)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    (Fintype.piFinset (fun _ : ι => primeCutoff F)).filter (fun f => (∏ i, f i) = b) =
      (Fintype.piFinset (fun _ : ι => primeCutoff X)).filter (fun f => (∏ i, f i) = b) := by
  ext f
  simp only [Finset.mem_filter,Fintype.mem_piFinset]
  constructor
  · rintro ⟨hf,he⟩
    refine ⟨fun i => mem_primeCutoff.mpr ⟨(mem_primeCutoff.mp (hf i)).1,?_⟩,he⟩
    have hd : f i ∣ b := he ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ i)
    exact (norm_le_of_dvd (primary_ne_zero hb) hd).trans hbX
  · rintro ⟨hf,he⟩
    exact ⟨fun i => mem_primeCutoff.mpr ⟨(mem_primeCutoff.mp (hf i)).1,
      (mem_primeCutoff.mp (hf i)).2.trans hXF⟩,he⟩

lemma distinguishedTupleCoefficient_restrict {X F : ℝ} (hXF : X ≤ F)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    distinguishedTupleCoefficient (fun _ : ι => primeCutoff F) W ψ w z b =
      distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z b := by
  unfold distinguishedTupleCoefficient orderedConvolution
  rw [primeTupleFiber_restrict hXF hb hbX]

lemma stoppedBeta_tuple_ball_restrict {X F : ℝ} (hXF : X ≤ F)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F) W ψ w z)
      ψ w selected b =
    stoppedBeta (primaryElementBall X) (primaryElementBall X)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z)
      ψ w selected b := by
  unfold stoppedBeta primaryPairCoefficient
  rw [primaryPairFiber_ball_restrict hXF hb hbX]
  apply Finset.sum_congr rfl
  intro p hp
  have hr := (mem_primaryElementBall.mp (Finset.mem_product.mp
    (Finset.mem_filter.mp hp).1).1)
  dsimp only
  rw [distinguishedTupleCoefficient_restrict hXF W ψ w z hr.1 hr.2]

lemma stoppedBeta_tuple_support (X : ℝ)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall X) (primaryElementBall X)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z)
      ψ w selected b =
    stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff X))
      (primaryElementBall X)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z)
      ψ w selected b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_congr_of_eq_on_inter
  · intro p hp hn
    have hp' := Finset.mem_filter.mp hp
    have hd := (Finset.mem_product.mp hp'.1).2
    have hr : p.1 ∉ orderedConvolutionSupport (fun _ : ι => primeCutoff X) := by
      intro hr
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,hd⟩,hp'.2⟩)
    have hz : distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z p.1 = 0 := by
      unfold distinguishedTupleCoefficient
      rw [orderedConvolution_eq_zero_of_not_mem _ _ hr,mul_zero]
    simp only [hz,zero_mul,ite_self]
  · intro p hp hn
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp hp'.1
    have hrp : primary p.1 := orderedPrimarySupport_primary _
      (fun _ _ h => (mem_primeCutoff.mp h).1.1) hr
    have hrX : norm p.1 ≤ X :=
      (norm_le_of_dvd (primary_ne_zero hb) ⟨p.2,hp'.2.symm⟩).trans hbX
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_primaryElementBall.mpr ⟨hrp,hrX⟩,hd⟩,hp'.2⟩)).elim
  · intro _ _ _
    rfl

/-- The actual finite-envelope beta, with its exact selected predicate,
is the analytic row at norm twist zero on every bounded primary product. -/
theorem stoppedBeta_eq_stoppedRowCoefficient {X F : ℝ} (hXF : X ≤ F)
    (W : ι → ℝ → ℂ) (w z : ℝ)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun i p => W i (norm p)) primeDetectorCutoff w z)
      primeDetectorCutoff w selected b =
      stoppedRowCoefficient X w z 0 W selected b := by
  rw [stoppedBeta_tuple_ball_restrict hXF,stoppedBeta_tuple_support X]
  · simp only [stoppedRowCoefficient,normTwist,zero_mul,Complex.ofReal_zero,
      Complex.exp_zero,mul_one]
  all_goals assumption

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingBinShift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport between geometric bins with two ambient norm cutoffs.
Below the smaller cutoff the bin labels differ by one fixed integer, and
the corresponding lower endpoints and prefix sets agree. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometricBinCount_mono {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) :
    geometricBinCount ρ X ≤ geometricBinCount ρ F := by
  exact Nat.ceil_mono (div_le_div_of_nonneg_right
    (Real.log_le_log hX hXF) (Real.log_pos hρ).le)

lemma geometricPrimeBin_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) {p : Eisenstein}
    (hp : primaryPrime p) (hpX : norm p ≤ X) :
    geometricPrimeBin ρ F p = geometricPrimeBin ρ X p +
      (geometricBinCount ρ F-geometricBinCount ρ X) := by
  have hc := geometricBinCount_mono hρ hX hXF
  have hpn : 0 < norm p := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (primaryPrime_norm_ge_two hp)
  have hk : ⌊Real.log (norm p)/Real.log ρ⌋₊ ≤ geometricBinCount ρ X :=
    (Nat.floor_mono (div_le_div_of_nonneg_right (Real.log_le_log hpn hpX)
      (Real.log_pos hρ).le)).trans (Nat.floor_le_ceil _)
  unfold geometricPrimeBin
  omega

lemma geometricBinLower_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (j : ℕ) :
    geometricBinLower ρ F (j+(geometricBinCount ρ F-geometricBinCount ρ X)) =
      geometricBinLower ρ X j := by
  have hc := geometricBinCount_mono hρ hX hXF
  unfold geometricBinLower
  congr 1
  omega

lemma geometricPrimeBin_finset_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X) (j : ℕ) :
    primeBin s (geometricPrimeBin ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) =
      primeBin s (geometricPrimeBin ρ X) j := by
  ext p
  by_cases hp : p ∈ s
  · simp only [primeBin,Finset.mem_filter,hp,true_and,
      geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2,
      Nat.add_right_cancel_iff]
  · simp only [primeBin,Finset.mem_filter,hp,false_and]

lemma geometricPrimeBin_prefix_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X) (j : ℕ) :
    primeBinPrefix s (geometricPrimeBin ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) =
      primeBinPrefix s (geometricPrimeBin ρ X) j := by
  ext p
  by_cases hp : p ∈ s
  · simp only [primeBinPrefix,Finset.mem_filter,hp,true_and,
      geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2,
      Nat.add_lt_add_iff_right]
  · simp only [primeBinPrefix,Finset.mem_filter,hp,false_and]

lemma geometricPrimeSurrogate_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X) :
    primeSurrogate s (geometricPrimeBin ρ F) (geometricBinLower ρ F) =
      primeSurrogate s (geometricPrimeBin ρ X) (geometricBinLower ρ X) := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2,
    geometricBinLower_shift hρ hX hXF]

lemma geometricStoppingPrimeSetTest_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X)
    (j k : ℕ) (Z : ℝ) (r : Eisenstein) :
    stoppingPrimeSetTest s (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k Z r ↔
    stoppingPrimeSetTest s (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k Z r := by
  have hall : (∀ p ∈ s, geometricPrimeBin ρ F p ≤
      j+(geometricBinCount ρ F-geometricBinCount ρ X)) ↔
      ∀ p ∈ s, geometricPrimeBin ρ X p ≤ j := by
    constructor
    · intro h p hp
      have he := h p hp
      rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2] at he
      omega
    · intro h p hp
      rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2]
      exact Nat.add_le_add_right (h p hp) _
  unfold stoppingPrimeSetTest
  rw [hall,geometricPrimeBin_finset_shift hρ hX hXF s hs,
    geometricPrimeSurrogate_shift hρ hX hXF s hs,geometricBinLower_shift hρ hX hXF]

lemma geometricStoppedSideTest_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) {d : Eisenstein}
    (hd : primary d) (hdX : norm d ≤ X)
    (j k h : ℕ) (Z Q : ℝ) (early : Bool) (r : Eisenstein) :
    stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k
      (h+(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early r d ↔
    stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early r d := by
  have hs (p : Eisenstein) (hp : p ∈ primaryPrimeFactors d) :
      primaryPrime p ∧ norm p ≤ X :=
    ⟨(primaryPrimeFactor_spec hd hp).1,
      (norm_le_of_dvd (primary_ne_zero hd) (primaryPrimeFactor_spec hd hp).2).trans hdX⟩
  have hprefix := geometricPrimeBin_prefix_shift hρ hX hXF (primaryPrimeFactors d) hs h
  have hsur := geometricPrimeSurrogate_shift hρ hX hXF
    (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ X) h)
    (fun p hp => hs p (Finset.mem_filter.mp hp).1)
  unfold stoppedSideTest stoppingSideTest
  rw [geometricStoppingPrimeSetTest_shift hρ hX hXF (primaryPrimeFactors d) hs,
    hprefix,hsur]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingSelectedScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual selected-side size bounds. A nonzero cutoff bounds the final
selected prime, while the stopping inequalities and geometric distortion
bound the complete coefficient scale. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_prime_norm_lt {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0) {w : ℝ} (hw : 0 < w)
    {d p : Eisenstein} (hp : p ∈ primaryPrimeFactors d)
    (hne : cutoffMoebius ψ w d ≠ 0) : norm p < 2*w := by
  have hprod := (mul_ne_zero_iff.mp hne).2
  change (∏ p ∈ primaryPrimeFactors d, (ψ (norm p/w):ℂ)) ≠ 0 at hprod
  have hterm := (Finset.prod_ne_zero_iff.mp hprod) p hp
  by_contra h
  have hx : 2 ≤ norm p/w := (le_div_iff₀ hw).mpr (by linarith)
  apply hterm
  simp only [hψ (norm p/w) hx,Complex.ofReal_zero]

lemma geometric_selected_norm_distortion {ρ X ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    {d : Eisenstein} (hd : primary d) (hs : Squarefree d) (hdX : norm d ≤ X) :
    norm d ≤ X^ε * primeSurrogate (primaryPrimeFactors d)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) := by
  let s := primaryPrimeFactors d
  have hcell (p : Eisenstein) (hp : p ∈ s) :
      0 ≤ geometricBinLower ρ X (geometricPrimeBin ρ X p) ∧
        geometricBinLower ρ X (geometricPrimeBin ρ X p) ≤ norm p ∧
          norm p ≤ ρ*geometricBinLower ρ X (geometricPrimeBin ρ X p) := by
    have hspec := primaryPrimeFactor_spec hd hp
    have hpX := (norm_le_of_dvd (primary_ne_zero hd) hspec.2).trans hdX
    exact ⟨pow_nonneg (zero_lt_one.trans hρ).le _,
      (geometricPrimeBin_cell hρ hρ₂ hspec.1 hpX).1,
      (geometricPrimeBin_cell hρ hρ₂ hspec.1 hpX).2.le⟩
  have hnorm := (primeSurrogate_norm_bounds s (geometricPrimeBin ρ X)
    (geometricBinLower ρ X) (zero_lt_one.trans hρ).le hcell).2
  have hprod : (∏ p ∈ s, p) = d := primaryPrimeFactors_prod hd hs
  rw [hprod] at hnorm
  have hcount : (2:ℝ)^s.card ≤ X :=
    (primary_prime_subset_two_pow_le hd hs (Finset.Subset.refl _)).trans hdX
  have hpower : ρ^s.card ≤ X^ε := by
    calc
      _ ≤ ((2:ℝ)^ε)^s.card := pow_le_pow_left₀ (zero_lt_one.trans hρ).le hsmall _
      _ = ((2:ℝ)^s.card)^ε := by
        rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_natCast_mul (by norm_num),mul_comm]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hcount hε
  exact hnorm.trans (mul_le_mul_of_nonneg_right hpower
    (Finset.prod_nonneg (fun p _ => pow_nonneg (zero_lt_one.trans hρ).le _)))

theorem stoppingSideTest_norm_bounds {ρ X Z w ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hZ : 0 < Z) (hw : 0 < w) {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {r d : Eisenstein} (hd : primary d) (hs : Squarefree d) (hdX : norm d ≤ X)
    {j k : ℕ} (hk : 1 ≤ k)
    (hstop : stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k Z r d)
    (hne : cutoffMoebius ψ w d ≠ 0) :
    Z ≤ norm (r*d) ∧ norm (r*d) ≤ 2*X^ε*w*Z := by
  have hX : 0 ≤ X := (norm_nonneg d).trans hdX
  have hbin : (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ X) j).Nonempty :=
    Finset.card_pos.mp (by rw [hstop.2.1]; omega)
  obtain ⟨p,hp⟩ := hbin
  obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
  have hspec := primaryPrimeFactor_spec hd hpd
  have hpX := (norm_le_of_dvd (primary_ne_zero hd) hspec.2).trans hdX
  have hell : geometricBinLower ρ X j < 2*w := by
    have hlower := (geometricPrimeBin_cell hρ hρ₂ hspec.1 hpX).1
    rw [hpj] at hlower
    exact hlower.trans_lt (cutoffMoebius_prime_norm_lt hψ hw hpd hne)
  have hellp : 0 < geometricBinLower ρ X j := pow_pos (zero_lt_one.trans hρ) _
  have hbefore := (div_lt_iff₀ hellp).mp hstop.2.2.1
  have hsur : primeSurrogate (primaryPrimeFactors d)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) ≤ norm d := by
    calc
      _ ≤ ∏ p ∈ primaryPrimeFactors d, norm p := by
        apply Finset.prod_le_prod
        · intro p _hp
          exact pow_nonneg (zero_lt_one.trans hρ).le _
        · intro p hp
          have hpp := primaryPrimeFactor_spec hd hp
          exact (geometricPrimeBin_cell hρ hρ₂ hpp.1
            ((norm_le_of_dvd (primary_ne_zero hd) hpp.2).trans hdX)).1
      _ = norm (∏ p ∈ primaryPrimeFactors d, p) := (norm_finset_prod _ _).symm
      _ = norm d := by rw [primaryPrimeFactors_prod hd hs]
  rw [norm_mul_eq]
  refine ⟨hstop.2.2.2.trans (mul_le_mul_of_nonneg_left hsur (norm_nonneg r)),?_⟩
  calc
    _ ≤ norm r*(X^ε * primeSurrogate (primaryPrimeFactors d)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) :=
      mul_le_mul_of_nonneg_left (geometric_selected_norm_distortion hρ hρ₂ hε hsmall hd hs hdX)
        (norm_nonneg r)
    _ = X^ε*(norm r*primeSurrogate (primaryPrimeFactors d)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) := by ring
    _ ≤ X^ε*(Z*geometricBinLower ρ X j) :=
      mul_le_mul_of_nonneg_left hbefore.le (Real.rpow_nonneg hX _)
    _ ≤ X^ε*(Z*(2*w)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hell.le hZ.le) (Real.rpow_nonneg hX _)
    _ = _ := by ring

theorem stoppedBeta_norm_bounds (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    {ψ : ℝ → ℝ} (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {ρ X Z Q w ε : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hZ : 0 < Z) (hw : 0 < w)
    (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    {j k h : ℕ} (hk : 1 ≤ k) (early : Bool) {b : Eisenstein}
    (hs : Squarefree b)
    (hne : stoppedBeta R D v ψ w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k h Z Q early) b ≠ 0) :
    Z ≤ norm b ∧ norm b ≤ 2*X^ε*w*Z := by
  unfold stoppedBeta primaryPairCoefficient at hne
  obtain ⟨p,hp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hp,hprod⟩ := Finset.mem_filter.mp hp
  obtain ⟨_hr,hd⟩ := Finset.mem_product.mp hp
  have hsel : stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early p.1 p.2 := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  rw [ite_eq_left hsel] at hterm
  have hcut := (mul_ne_zero_iff.mp hterm).2
  have hsq : Squarefree (p.1*p.2) := by rwa [hprod]
  have hh := stoppingSideTest_norm_bounds hρ hρ₂ hε hsmall hZ hw hψ
    (hD p.2 hd).1 hsq.of_mul_right (hD p.2 hd).2 hk hsel.1 hcut
  rwa [hprod] at hh

/-- A fixed ambient dilation has the same strict selected-scale range.
The cutoff parameter remains X^ξ while the geometric distortion is
measured on the actual ambient envelope C*X. -/
theorem eventually_two_stage_stopped_dyad_range_dilation {ξ ε C : ℝ}
    (hC : 0 < C) (hgap : ξ+ε < 1/100) :
    ∀ᶠ X : ℝ in atTop, ∀ (b Z N : ℝ),
      (Z = X^(36/100:ℝ) ∨ Z = X^(38/100:ℝ)) →
      Z ≤ N → N ≤ 2*(C*X)^ε*X^ξ*Z → b/2 ≤ N → N ≤ b →
      X^(35/100:ℝ) ≤ b ∧ b ≤ X^(39/100:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show ε+ξ+38/100 < (39/100:ℝ) by linarith)
      (4*C^ε)] with X hX hlarge
  intro b Z N hZ hZN hN hbN hNb
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hZlo : X^(35/100:ℝ) ≤ Z := by
    rcases hZ with rfl | rfl
    all_goals exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hZhi : Z ≤ X^(38/100:ℝ) := by
    rcases hZ with rfl | rfl
    · exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    · exact le_rfl
  refine ⟨hZlo.trans (hZN.trans hNb),?_⟩
  have hh : 2*N ≤ X^(39/100:ℝ) := by
    calc
      2*N ≤ 4*(C*X)^ε*X^ξ*Z := by linarith
      _ ≤ 4*(C*X)^ε*X^ξ*X^(38/100:ℝ) :=
        mul_le_mul_of_nonneg_left hZhi (by positivity)
      _ = (4*C^ε)*X^(ε+ξ+38/100:ℝ) := by
        rw [Real.mul_rpow hC.le hXp.le,
          Real.rpow_add hXp,Real.rpow_add hXp]
        ring
      _ ≤ _ := hlarge
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingCoefficientShift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recovering the smaller-envelope labels on actual nonzero stopped
coefficients, and transporting the independent remaining-side coefficient.
All finite support and both stopping thresholds stay unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppingSideTest_label_shift_bound {ρ X F Z : ℝ}
    (hρ : 1 < ρ) (hX : 0 < X) (hXF : X ≤ F)
    {d r : Eisenstein} (hd : primary d) (hdX : norm d ≤ X)
    {j k : ℕ} (hk : 1 ≤ k)
    (hs : stoppingSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k Z r d) :
    geometricBinCount ρ F-geometricBinCount ρ X ≤ j := by
  have hne : (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ F) j).Nonempty :=
    Finset.card_pos.mp (by rw [hs.2.1]; omega)
  obtain ⟨p,hp⟩ := hne
  obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
  have hprime := primaryPrimeFactor_spec hd hpd
  have hpX := (norm_le_of_dvd (primary_ne_zero hd) hprime.2).trans hdX
  have hshift := geometricPrimeBin_shift hρ hX hXF hprime.1 hpX
  rw [hpj] at hshift
  omega

lemma stoppedBeta_label_shift_bound (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) {ρ X F Z Q : ℝ}
    (hρ : 1 < ρ) (hX : 0 < X) (hXF : X ≤ F)
    (hD : ∀ d ∈ D, primary d) {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X)
    {j k h : ℕ} (hk : 1 ≤ k) (early : Bool)
    (hne : stoppedBeta R D v ψ w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
        j k h Z Q early) b ≠ 0) :
    geometricBinCount ρ F-geometricBinCount ρ X ≤ j := by
  unfold stoppedBeta primaryPairCoefficient at hne
  obtain ⟨p,hp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
  obtain ⟨_hr,hd⟩ := Finset.mem_product.mp hp
  have hs : stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      j k h Z Q early p.1 p.2 := by
    by_contra hs
    exact hterm (ite_eq_right hs)
  have hdb : p.2 ∣ b := ⟨p.1,by rw [mul_comm,he]⟩
  exact stoppingSideTest_label_shift_bound hρ hX hXF (hD p.2 hd)
    ((norm_le_of_dvd (primary_ne_zero hb) hdb).trans hbX) hk hs.1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry derived from a surviving term of the original stopped dyad. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedStoppedSide_spec {X : ℝ} {n : Eisenstein}
    (hn : n ∈ distinguishedStoppedSide X) :
    primary n ∧ Squarefree n ∧ norm n ≤ Real.exp primeProductWeights.radius*X := by
  obtain ⟨hp,hs,hnorm⟩ := Finset.mem_filter.mp hn
  exact ⟨primaryPairSupport_primary _ _
    (fun _ hh => (mem_primaryElementBall.mp hh).1)
    (fun _ hh => (mem_primaryElementBall.mp hh).1) hp,hs,hnorm⟩

lemma distinguishedStoppedBeta_as_weights (i : ℕ) (ρ ξ X : ℝ) (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) :
    distinguishedStoppedBeta i ρ ξ X h early d q =
      stoppedBeta (centralPrimaryFactors X) (centralPrimaryFactors X)
        (distinguishedTupleCoefficient
          (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
          (fun a p => distinguishedStoppingWeights d a (norm p))
          primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))) primeDetectorCutoff (X^ξ)
        (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X))
          q.1 q.2.1 h (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early) := by
  unfold distinguishedStoppedBeta distinguishedScaleCoefficient
  have he : (fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(d a).val)) =
      (fun a p => distinguishedStoppingWeights d a (norm p)) := by
    funext a p
    exact (distinguishedStoppingWeights_at d a p).symm
  rw [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularScaleFirstStoppedGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-angular low-height stopping rows, retaining the original
coefficients, product support, and inverse-binomial factors. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angular_distinguishedStoppedDyad_witness (ℓ : ℤ) (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ)
    (hne : angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h early d q j k ≠ 0) :
    ∃ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
      ∃ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
        distinguishedStoppedBeta i ρ ξ X h early d q b ≠ 0 ∧
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) ≠ 0 := by
  obtain ⟨a,ha,hsum⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨b,hb,ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨a,ha,b,hb,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ht).1).2,?_⟩
  intro hz
  apply ht
  simp only [hz,ite_self,mul_zero]

theorem eventually_angular_distinguishedStoppedDyad_geometry (ℓ : ℤ) {ρ ξ ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hgap : ξ+ε < 1/100) :
    ∀ᶠ X : ℝ in atTop, ∀ (i Ct : ℕ) (H : ℝ) (h : ℕ) (early : Bool)
      (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ) (j k : ℕ), 1 ≤ q.2.1 →
      angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h early d q j k ≠ 0 →
      X^(7/20:ℝ) ≤ stoppedNormDyadLength k ∧
      stoppedNormDyadLength k ≤ X^(39/100:ℝ) ∧
      stoppedNormDyadLength k ≤ X ∧
      X/16 ≤ (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ∧
      (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ≤ 16*X ∧
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ q.1 := by
  filter_upwards [eventually_two_stage_stopped_dyad_range_dilation
    (Real.exp_pos primeProductWeights.radius) hgap,eventually_ge_atTop (1:ℝ)] with X hr hX
  intro i Ct H h early d q j k hk hne
  obtain ⟨a,ha,b,hb,hβ,hK⟩ := angular_distinguishedStoppedDyad_witness ℓ i ρ ξ Ct H X h early d q j k hne
  have has := distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1
  have hbs := distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1
  have hab := stoppedNormDyad_outer_bounds ha has.1
  have hbb := stoppedNormDyad_outer_bounds hb hbs.1
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  have hsize := stoppedBeta_norm_bounds (centralPrimaryFactors X) (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) (fun x hx => primeDetectorCutoff_zero hx)
    hρ hρ₂ hε hsmall
    (show 0 < (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) by split <;> positivity)
    (Real.rpow_pos_of_pos hXp ξ)
    (fun n hn => mem_primaryElementBall.mp hn) hk early hbs.2.1 hβ
  have hZ : (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) = X^(36/100:ℝ) ∨
      (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) = X^(38/100:ℝ) := by
    cases early <;> norm_num
  have hBr := hr (stoppedNormDyadLength k) _ (norm b) hZ hsize.1 hsize.2 hbb.1 hbb.2
  have hBX : stoppedNormDyadLength k ≤ X := hBr.2.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (show (39/100:ℝ) ≤ 1 by norm_num))
  have hKR := centeredHeightKernel_norm_range ℓ H _ hXp hK
  have hprod := stopped_dyad_product_range
    (div_nonneg (stoppedNormDyadLength_pos j).le (by norm_num))
    (stoppedNormDyadLength_pos k).le
    (show stoppedNormDyadLength j/2 ≤ norm a ∧ norm a ≤ 2*(stoppedNormDyadLength j/2) by
      constructor
      · exact hab.1
      · nlinarith [hab.2]) hbb ⟨hKR.1.le,hKR.2.le⟩
  refine ⟨by simpa only [show (35/100:ℝ)=7/20 by norm_num] using hBr.1,
    hBr.2,hBX,by linarith [hprod.1],by linarith [hprod.2],?_⟩
  exact stoppedBeta_label_shift_bound _ _ _ _ _ hρ hXp hXF
    (fun n hn => (mem_primaryElementBall.mp hn).1) hbs.1 (hbb.2.trans hBX) hk early hβ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedIntervalRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of the sharp stopped side to the full analytic
interval at exclusion e=1. Coefficients vanish off their actual product
support, so the interval extension adds no term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedNormDyad_mem_iff {S : Finset Eisenstein} {j : ℕ} {n : Eisenstein}
    (hN : 2 ≤ norm n) :
    n ∈ stoppedNormDyad S j ↔
      n ∈ S ∧ stoppedNormDyadLength j/2 < norm n ∧ norm n ≤ stoppedNormDyadLength j := by
  constructor
  · intro hn
    exact ⟨(Finset.mem_filter.mp hn).1,stoppedNormDyad_bounds hn hN⟩
  · rintro ⟨hn,hlo,hhi⟩
    apply Finset.mem_filter.mpr
    refine ⟨hn,?_⟩
    have he : stoppedNormDyadLength j/2 = (2:ℝ)^j := by
      unfold stoppedNormDyadLength
      rw [pow_succ]
      ring
    rw [he] at hlo
    have hl : (2:ℕ)^j < normNat n := by
      exact_mod_cast (show (2:ℝ)^j < (normNat n:ℝ) by simpa only [normNat_cast] using hlo)
    have hu : normNat n ≤ (2:ℕ)^(j+1) := by
      exact_mod_cast (show (normNat n:ℝ) ≤ (2:ℝ)^(j+1) by
        simpa only [normNat_cast,stoppedNormDyadLength] using hhi)
    exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)

lemma primaryPairSupport_self_of_mem {F : ℝ} (hF : 1 ≤ F)
    {n : Eisenstein} (hn : n ∈ primaryElementBall F) :
    n ∈ primaryPairSupport (primaryElementBall F) (primaryElementBall F) := by
  refine Finset.mem_image.mpr ⟨(n,1),Finset.mem_product.mpr ⟨hn,?_⟩,by simp⟩
  exact mem_primaryElementBall.mpr ⟨primary_one,by simpa only [norm_one_eq] using hF⟩

lemma stoppedRowCoefficient_eq_zero_of_not_mem (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) {n : Eisenstein}
    (hn : n ∉ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff X))
      (primaryElementBall X)) :
    stoppedRowCoefficient X w z u W selected n = 0 := by
  unfold stoppedRowCoefficient stoppedBeta primaryPairCoefficient
  suffices hs : (∑ p ∈ primaryPairFiber
      (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X) n,
      if selected p.1 p.2 then
        distinguishedTupleCoefficient (fun _ : ι => primeCutoff X)
          (fun i p => W i (norm p)) primeDetectorCutoff w z p.1 *
            cutoffMoebius primeDetectorCutoff w p.2 else 0) = 0 by rw [hs,zero_mul]
  apply Finset.sum_eq_zero
  intro p hp
  exact (hn (Finset.mem_image.mpr ⟨p,(Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩)).elim

theorem stoppedBeta_interval_sum_to_row {X F B : ℝ}
    (hX : 1 ≤ X) (hXF : X ≤ F) (hBX : B ≤ X)
    (W : ι → ℝ → ℂ) (w z a : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (K : Eisenstein → ℂ) :
    (∑ n ∈ (primaryPairSupport (primaryElementBall F) (primaryElementBall F)).filter
        (fun n => Squarefree n ∧ a < norm n ∧ norm n ≤ B),
      stoppedBeta (primaryElementBall F) (primaryElementBall F)
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
          (fun i p => W i (norm p)) primeDetectorCutoff w z)
        primeDetectorCutoff w selected n*K n) =
      ∑ n ∈ stoppedIntervalSupport ι X a B 1,
        stoppedRowCoefficient X w z 0 W selected n*K n := by
  let Q := primaryPairSupport (primaryElementBall F) (primaryElementBall F)
  have hQ (n : Eisenstein) (hn : n ∈ Q) : primary n :=
    primaryPairSupport_primary _ _ (fun _ h => (mem_primaryElementBall.mp h).1)
      (fun _ h => (mem_primaryElementBall.mp h).1) hn
  apply Finset.sum_congr_of_eq_on_inter
  · intro n hn hnot
    obtain ⟨hn,hs,hlo,hhi⟩ := Finset.mem_filter.mp hn
    have hp := hQ n hn
    have hb := stoppedBeta_eq_stoppedRowCoefficient hXF W w z selected hp (hhi.trans hBX)
    rw [hb]
    have hsupport : n ∉ primaryPairSupport
        (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X) := by
      intro hh
      apply hnot
      apply Finset.mem_filter.mpr
      exact ⟨hh,hs,isCoprime_one_right,hlo,hhi⟩
    rw [stoppedRowCoefficient_eq_zero_of_not_mem X w z 0 W selected hsupport,zero_mul]
  · intro n hn hnot
    obtain ⟨hp,hs,hhi⟩ := stoppedIntervalSupport_spec X a B 1 hn
    have hh := Finset.mem_filter.mp hn
    have hnQ : n ∈ Q := primaryPairSupport_self_of_mem (hX.trans hXF)
      (mem_primaryElementBall.mpr ⟨hp,(hhi.trans hBX).trans hXF⟩)
    exact (hnot (Finset.mem_filter.mpr ⟨hnQ,hs,hh.2.2.2.1,hhi⟩)).elim
  · intro n hn _
    obtain ⟨hn,_hs,_hlo,hhi⟩ := Finset.mem_filter.mp hn
    rw [stoppedBeta_eq_stoppedRowCoefficient hXF W w z selected (hQ n hn) (hhi.trans hBX)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDyadRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original squarefree sharp dyad is exactly the full analytic
stopped interval. Its possible norm-one term vanishes by the genuine
stopping lower bound, rather than being discarded from the finite sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedRowCoefficient_geometric_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (W : ι → ℝ → ℂ) (w z u Z Q : ℝ)
    (j k h : ℕ) (early : Bool) (n : Eisenstein) :
    stoppedRowCoefficient X w z u W
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k
        (h+(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) n =
      stoppedRowCoefficient X w z u W
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          j k h Z Q early) n := by
  unfold stoppedRowCoefficient
  congr 1
  apply stoppedBeta_selected_congr
  intro r _ d hd _
  have hdp := mem_primaryElementBall.mp hd
  exact geometricStoppedSideTest_shift hρ hX hXF hdp.1 hdp.2 j k h Z Q early r

lemma stoppedRowCoefficient_geometric_shift_of_bounds {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (W : ι → ℝ → ℂ) (w z u Z Q : ℝ)
    (j k h : ℕ) (early : Bool) (n : Eisenstein)
    (hj : geometricBinCount ρ F-geometricBinCount ρ X ≤ j)
    (hh : geometricBinCount ρ F-geometricBinCount ρ X ≤ h) :
    stoppedRowCoefficient X w z u W
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early) n =
      stoppedRowCoefficient X w z u W
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
          (h-(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) n := by
  simpa only [Nat.sub_add_cancel hj,Nat.sub_add_cancel hh] using
    stoppedRowCoefficient_geometric_shift hρ hX hXF W w z u Z Q
      (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
      (h-(geometricBinCount ρ F-geometricBinCount ρ X)) early n

theorem stoppedBeta_sharp_dyad_to_row {ρ X F w Z Q : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X) (hXF : X ≤ F)
    (hw : 0 < w) (hZ : 2 ≤ Z) (W : ι → ℝ → ℂ) (z : ℝ)
    (j k h i : ℕ) (hk : 1 ≤ k) (early : Bool) (K : Eisenstein → ℂ)
    (hBX : stoppedNormDyadLength i ≤ X) :
    let selected := stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      j k h Z Q early
    let β := stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun a p => W a (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w selected
    (∑ n ∈ stoppedNormDyad
        ((primaryPairSupport (primaryElementBall F) (primaryElementBall F)).filter
          (fun n => Squarefree n ∧ norm n ≤ F)) i, β n*K n) =
      ∑ n ∈ stoppedIntervalSupport ι X (stoppedNormDyadLength i/2)
        (stoppedNormDyadLength i) 1,
        stoppedRowCoefficient X w z 0 W selected n*K n := by
  let selected := stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
    j k h Z Q early
  let β := stoppedBeta (primaryElementBall F) (primaryElementBall F)
    (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
      (fun a p => W a (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w selected
  let R := primaryPairSupport (primaryElementBall F) (primaryElementBall F)
  let B := stoppedNormDyadLength i
  change (∑ n ∈ stoppedNormDyad (R.filter (fun n => Squarefree n ∧ norm n ≤ F)) i,
      β n*K n) = ∑ n ∈ stoppedIntervalSupport ι X (B/2) B 1,
        stoppedRowCoefficient X w z 0 W selected n*K n
  have hB : 2 ≤ B := by
    have hh : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
    dsimp [B,stoppedNormDyadLength]
    rw [pow_succ]
    nlinarith
  have hlow (n : Eisenstein) (hs : Squarefree n) (hne : β n ≠ 0) :
      2 ≤ norm n := by
    have hh := stoppedBeta_norm_bounds (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun a p => W a (norm p)) primeDetectorCutoff w z)
      (fun x hx => primeDetectorCutoff_zero hx) hρ hρ₂ (by norm_num : (0:ℝ) ≤ 1)
      (by simpa using hρ₂) (by linarith : 0 < Z) hw
      (fun d hd => mem_primaryElementBall.mp hd) hk early hs hne
    exact hZ.trans hh.1
  have heq : (∑ n ∈ stoppedNormDyad (R.filter (fun n => Squarefree n ∧ norm n ≤ F)) i,
      β n*K n) = ∑ n ∈ R.filter (fun n => Squarefree n ∧ B/2 < norm n ∧ norm n ≤ B),
        β n*K n := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro n hn hnot
      by_cases hz : β n = 0
      · rw [hz,zero_mul]
      · have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.1
        have hr := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
        have hd := stoppedNormDyad_bounds hn (hlow n hs hz)
        exact (hnot (Finset.mem_filter.mpr ⟨hr,hs,hd⟩)).elim
    · intro n hn hnot
      obtain ⟨hr,hs,hlo,hhi⟩ := Finset.mem_filter.mp hn
      have hone : (1:ℝ) < norm n := lt_of_le_of_lt (by linarith) hlo
      have hnat : 1 < normNat n := by
        exact_mod_cast (show (1:ℝ) < (normNat n:ℝ) by simpa only [normNat_cast] using hone)
      have hn2 : (2:ℝ) ≤ norm n := by
        rw [←normNat_cast]
        exact_mod_cast (show 2 ≤ normNat n by omega)
      apply (hnot ((stoppedNormDyad_mem_iff hn2).mpr ?_)).elim
      exact ⟨Finset.mem_filter.mpr ⟨hr,hs,(hhi.trans hBX).trans hXF⟩,hlo,hhi⟩
    · intro _ _ _
      rfl
  rw [heq]
  exact stoppedBeta_interval_sum_to_row hX hXF hBX W w z (B/2) selected K

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedShiftedDyad
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact original-envelope sharp dyad as a smaller-envelope analytic
row, including the selected-bin and failed-prefix boundary shifts. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_shifted_sharp_dyad_to_row {ρ X F w Z Q : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X) (hXF : X ≤ F)
    (hw : 0 < w) (hZ : 2 ≤ Z) (W : ι → ℝ → ℂ) (z : ℝ)
    (j k h i : ℕ) (hk : 1 ≤ k) (early : Bool) (K : Eisenstein → ℂ)
    (hBX : stoppedNormDyadLength i ≤ X)
    (hj : geometricBinCount ρ F-geometricBinCount ρ X ≤ j)
    (hh : geometricBinCount ρ F-geometricBinCount ρ X ≤ h) :
    let β := stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun a p => W a (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early)
    (∑ n ∈ stoppedNormDyad
        ((primaryPairSupport (primaryElementBall F) (primaryElementBall F)).filter
          (fun n => Squarefree n ∧ norm n ≤ F)) i, β n*K n) =
      ∑ n ∈ stoppedIntervalSupport ι X (stoppedNormDyadLength i/2)
        (stoppedNormDyadLength i) 1,
        stoppedRowCoefficient X w z 0 W
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
            (h-(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) n*K n := by
  dsimp only
  calc
    _ = ∑ n ∈ stoppedIntervalSupport ι X (stoppedNormDyadLength i/2)
        (stoppedNormDyadLength i) 1,
        stoppedRowCoefficient X w z 0 W
          (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early) n*K n :=
      stoppedBeta_sharp_dyad_to_row hρ hρ₂ hX hXF hw hZ W z j k h i hk early K hBX
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [stoppedRowCoefficient_geometric_shift_of_bounds hρ (zero_lt_one.trans_le hX)
        hXF W w z 0 Z Q j k h early n hj hh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularScaleFirstStoppedTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-angular low-height stopping rows, retaining the original
coefficients, product support, and inverse-binomial factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_distinguishedStoppedDyad_to_row (ℓ : ℤ) (i : ℕ) {ρ ξ X : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X) (Ct : ℕ) (H : ℝ)
    (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) (hk : 1 ≤ q.2.1)
    (hZ : 2 ≤ (if early then X^(9/25:ℝ) else X^(38/100:ℝ)))
    (hBX : stoppedNormDyadLength k ≤ X)
    (hj : geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ q.1)
    (hh : geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h) :
    angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h early d q j k =
      ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
        ∑ b ∈ stoppedIntervalSupport (Fin i) X (stoppedNormDyadLength k/2)
          (stoppedNormDyadLength k) 1,
          distinguishedStoppedAlpha ρ ξ X q a*
            stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
              (distinguishedShiftedSideTest ρ X h early q) b*
            centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  unfold angular_distinguishedStoppedDyad
  apply Finset.sum_congr rfl
  intro a ha
  have hap := (distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1).1
  calc
    _ = distinguishedStoppedAlpha ρ ξ X q a *
        ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
          distinguishedStoppedBeta i ρ ξ X h early d q b*
            centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [←mul_assoc]
      congr 1
      exact centeredHeightKernel_envelope ℓ primeProductEnvelope hXp
        (primeProductWeights.upper_support ()) H ((1+Real.log X)^Ct) X
        (primary_mul hap (distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1).1)
    _ = distinguishedStoppedAlpha ρ ξ X q a *
        ∑ b ∈ stoppedIntervalSupport (Fin i) X (stoppedNormDyadLength k/2)
          (stoppedNormDyadLength k) 1,
          stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
            (distinguishedShiftedSideTest ρ X h early q) b*
            centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) := by
      congr 1
      simpa only [distinguishedStoppedBeta_as_weights,distinguishedStoppedSide,
        stoppedFactorSupport,centralPrimaryFactors,distinguishedShiftedSideTest] using
        stoppedBeta_shifted_sharp_dyad_to_row hρ hρ₂ hX hXF
          (Real.rpow_pos_of_pos hXp ξ) hZ (distinguishedStoppingWeights d) (X^(2/5:ℝ))
          q.1 q.2.1 h k hk early
          (fun b => centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b))
          hBX hj hh
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredProductHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-height integral of a literal centered product polynomial.
The product envelope is separated at its actual Mellin frequency. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem centered_product_low_integral (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (W : ℝ → ℂ)
    (X X₀ T : ℝ) {H : ℝ} (hH : 0 < H) :
    (∑ a ∈ A, ∑ b ∈ B, α a*β b*centeredHeightKernel ℓ W H T X X₀ (a*b)) =
      ∫ t : ℝ, (lowHeightWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        centeredProductSmoothed A B α β ℓ W X t := by
  let c : Eisenstein × Eisenstein → ℂ := fun q =>
    α q.1*β q.2*theta ℓ (q.1*q.2)*centeredGauss (q.1*q.2)*W (norm (q.1*q.2)/X)
  have hb := height_norm_polynomial_integral (A.product B) c (fun q => q.1*q.2)
    (lowHeightWeight H T) (lowHeightWeight_integrable hH T) (Real.log X₀)
  simp only [Finset.product_eq_sprod,Finset.sum_product] at hb
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, c (a,b)*heightFourierIntegral (lowHeightWeight H T)
        (Real.log (norm (a*b))-Real.log X₀) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp [c,centeredHeightKernel]
      ring
    _ = _ := by
      rw [hb]
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      unfold centeredProductSmoothed
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp [c]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedHeightFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicative angular phases in the two coefficients give exactly
 the angular phase of the original centered height kernel. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma centeredHeightSum_angular_factors (ℓ : ℤ) (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : ℝ → ℂ) (H T X X₀ : ℝ) :
    (∑ a ∈ A, ∑ b ∈ B, (α a*theta ℓ a)*(β b*theta ℓ b)*
      centeredHeightKernel 0 W H T X X₀ (a*b)) =
    ∑ a ∈ A, ∑ b ∈ B, α a*β b*centeredHeightKernel ℓ W H T X X₀ (a*b) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [centeredHeightKernel,theta_zero,theta_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedStoppingMesh
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed geometric mesh meets the inverse logarithmic width condition
of the stopped analytic estimate for all sufficiently large parameters. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_fixed_stopping_mesh {ρ : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) :
    ∀ᶠ X : ℝ in atTop,
      0 < ρ-1 ∧ ρ-1 ≤ 1 ∧ (Real.log X)^(-(1:ℝ)) ≤ ρ-1 := by
  have hδ : 0 < ρ-1 := by linarith
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1/(ρ-1)),
    eventually_gt_atTop (1:ℝ)] with X hbound hX
  refine ⟨hδ,by linarith,?_⟩
  have hlog : 0 < Real.log X := Real.log_pos hX
  rw [Real.rpow_neg_one]
  rw [←one_div]
  apply (div_le_iff₀ hlog).mpr
  have he := (div_le_iff₀ hδ).mp hbound
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstEarlyNegligible
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single logarithmic boundary makes all finitely many early stopped
arities negligible. No boundary is chosen before the analytic constants. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stopped_log_quotient_normalize (d k : ℕ) {L K P : ℝ}
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hP : 0 ≤ P) :
    (1+L)^d*(K*P/L^(d+k)) ≤ (K*2^(d+k))*P/(1+L)^k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hL1 : 0 < 1+L := by linarith
  apply (le_div_iff₀ (pow_pos hL1 k)).mpr
  calc
    _ = (K*P)*((1+L)^(d+k)/L^(d+k)) := by
      rw [pow_add]
      field_simp
      ring
    _ ≤ (K*P)*2^(d+k) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hP)
      apply (div_le_iff₀ (pow_pos hLp (d+k))).mpr
      rw [←mul_pow]
      exact pow_le_pow_left₀ hL1.le (by linarith : 1+L ≤ 2*L) _
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralAngularStoppedProductLowSaving
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full stopped product estimate integrated against the actual
low-height multiplier. A finite logarithmic loss is paid explicitly. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem angular_stopped_product_low_log_saving_actual
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℝ) (hΦnn : ∀ x, 0 ≤ Φ x)
    (hΦ : HasCompactSupport (fun x => (Φ x:ℂ)))
    (hΦpos : tsupport (fun x => (Φ x:ℂ)) ⊆ Set.Ioi 0)
    (hΦ' : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)))
    (hΦone : ∀ x ∈ Set.Icc (1:ℝ) 2, 1 ≤ Φ x)
    {RΦ : ℝ} (hcut : ∀ x, RΦ < x → Φ x = 0)
    (Ω : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (hΩpos : tsupport Ω ⊆ Set.Ioi 0)
    (hΩsm : ContDiff ℝ ∞ Ω) (k Ct : ℕ) :
    ∃ (d G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b v A X₀ H : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X → 0 < X₀ →
      0 ≤ v → 1+v ≤ (Real.log X)^F → 0 < H →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ v) →
      2*b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(15*(2*(k+Ct)+d)) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ (E₀ U P : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
        (remaining : Eisenstein → Prop),
      (∀ c ∈ E₀, primary c) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∀ c ∈ P, primary c ∧ Squarefree c ∧ A ≤ norm c ∧ norm c ≤ 2*A) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖∑ a ∈ P, ∑ b ∈ S, angularStoppedAlpha ℓ E₀ U ψ w remaining a*β b*
        centeredHeightKernel 0 Ω H ((1+Real.log X)^Ct) X₀ X₀ (a*b)‖ ≤
        K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨d,G,K,hK,hbound⟩ := angular_stopped_product_bilinear_log_saving_actual (ι := ι)
    hpnt hEF ℓ hℓ hMV hC hHuxley  hGamma hξ hξz hκ hF hJ
    Φ hΦnn hΦ hΦpos hΦ' hΦone hcut Ω hΩ hΩpos hΩsm (k+Ct) (Ct+2)
  let K' := (8/3)*Real.log 2*(2:ℝ)^Ct*K
  refine ⟨d,G,K',by dsimp [K']; positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (Real.exp ((2:ℝ)^(Ct+2)))] with X hb hX
  intro δ b v A X₀ H hδ hδ1 hwidth hb2 hbκ hbX hX₀ hv hvF hH
    W hW hWs hWd hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hrough E₀ U P ψ w
    remaining hE₀ hψ hP
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let α := angularStoppedAlpha ℓ E₀ U ψ w remaining
  let L := Real.log X
  let T := (1+L)^Ct
  have hlog : (2:ℝ)^(Ct+2) ≤ L := by
    simpa only [L,Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hL1 : 1 ≤ L := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans hlog
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hT : 0 < T := by dsimp [T]; positivity
  have hTc : T ≤ (2:ℝ)^Ct*L^Ct := by
    dsimp [T]
    rw [←mul_pow]
    gcongr
    linarith
  have hphase (t : ℝ) (ht : t ∈ Set.Icc (-(4/3)*T) ((4/3)*T)) :
      |t| ≤ L^(Ct+2) := by
    have ha : |t| ≤ (4/3)*T := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
    have hc : (4/3)*(2:ℝ)^Ct ≤ L^2 := by
      have hpow : (2:ℝ)^(Ct+2) = (2:ℝ)^Ct*4 := by rw [pow_add]; norm_num
      have hbig : (4/3)*(2:ℝ)^Ct ≤ L := by nlinarith [hlog,hpow,pow_nonneg (by norm_num : (0:ℝ) ≤ 2) Ct]
      exact hbig.trans (by nlinarith)
    calc
      _ ≤ (4/3)*((2:ℝ)^Ct*L^Ct) := ha.trans (mul_le_mul_of_nonneg_left hTc (by norm_num))
      _ ≤ L^2*L^Ct := by nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg hLp.le Ct)]
      _ = _ := by rw [pow_add]; ring
  have hsize : 0 ≤ K*A^(5/6:ℝ)*b^(5/6:ℝ)/L^(k+Ct) := by
    have hbp : 0 < b := by linarith
    have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le (by linarith [Real.rpow_nonneg hbp.le (3/2:ℝ)] : b^(3/2:ℝ) ≤ A)
    positivity
  rw [centered_product_low_integral P S α β 0 Ω X₀ X₀ T hH]
  have hi := lowHeightWeight_integral_bound H hT hsize
    (fun t => Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
      centeredProductSmoothed P S α β 0 Ω X₀ t) (by
        intro t ht
        rw [norm_mul]
        have hephase : ‖Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)‖ = 1 := by
          simp only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
            Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,Real.exp_zero]
        rw [hephase,one_mul]
        exact hb δ b t v A X₀ hδ hδ1 hwidth hb2 hbκ hbX hX₀ hv (hphase t ht) hvF
          W hW hWs hWd hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hrough E₀ U P ψ w
          remaining hE₀ hψ hP)
  have heint : (fun t => (lowHeightWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
      centeredProductSmoothed P S α β 0 Ω X₀ t) =
      (fun t => lowHeightWeight H T t*(Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        centeredProductSmoothed P S α β 0 Ω X₀ t)) := by funext t; ring
  rw [heint]
  apply hi.trans
  calc
    _ ≤ (8/3)*Real.log 2*((2:ℝ)^Ct*L^Ct)*
        (K*A^(5/6:ℝ)*b^(5/6:ℝ)/L^(k+Ct)) := by gcongr
    _ = K'*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
      dsimp [K',L]
      rw [pow_add]
      field_simp [show Real.log X ≠ 0 from hLp.ne']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralAngularStoppedOrdinaryLowSaving
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordinary side lengths and actual distinguished partition
weights satisfy every analytic parameter condition of the stopped bound. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem angular_ordinary_stopped_low_kernel_bound_actual (ℓ : ℤ) (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    {C ξ ρ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (k Ct : ℕ) :
    ∃ (G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (N : ℕ) (d : Fin i → Fin N) (A b H : ℝ),
      X/16 ≤ A*b → A*b ≤ 16*X →
      X^(7/20:ℝ) ≤ b → b ≤ X^(39/100:ℝ) → 0 < H →
      ∀ (j q h : ℕ) (Z Q : ℝ) (early : Bool), j ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower ρ X h) →
      ∀ (E₀ U P : Finset Eisenstein) (remaining : Eisenstein → Prop),
      (∀ e ∈ E₀, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
      let S := stoppedIntervalSupport (Fin i) X (b/2) b 1
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j q h Z Q early)
      ‖∑ a ∈ P, ∑ b ∈ S, stoppedAlpha E₀ U primeDetectorCutoff (X^ξ) remaining a*β b*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b)‖ ≤
        K*X^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨V,hV,hweights⟩ := distinguishedStoppingWeights_uniform
  obtain ⟨d₀,G,K,hK,hbound⟩ := angular_stopped_product_low_log_saving_actual (ι := Fin i)
    (κ := 1/4) (E := 0) (F := 1) (J := 1)
    hpnt hEF ℓ hℓ hMV hC hHuxley  hGamma hξ hξz (by norm_num) (by norm_num) (by norm_num)
    (dispersionCutoff 4) (dispersionCutoff_nonneg 4) (dispersionCutoff_complex_compact 4)
    (dispersionCutoff_positive_support 4) (dispersionCutoff_complex_smooth 4)
    (fun x hx => by rw [dispersionCutoff_one ⟨hx.1,by linarith [hx.2]⟩])
    (RΦ := 5) (fun x hx => dispersionCutoff_high (by linarith))
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth k Ct
  refine ⟨G,K*(16:ℝ)^(5/6:ℝ),by positivity,?_⟩
  filter_upwards [hbound,eventually_stopped_actual_range (15*(2*(k+Ct)+d₀)),
    eventually_fixed_stopping_mesh hρ hρ₂,
    Real.tendsto_log_atTop.eventually_ge_atTop (1+V),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_ge_atTop 2,
    eventually_gt_atTop (1:ℝ)] with X hb hr hw hVX htwo hX
  intro N d A b H hp hp' hblo hbhi hH j q h Z Q early hj hrough E₀ U P remaining hE₀ hP
  dsimp only
  have hXp : 0 < X := zero_lt_one.trans hX
  have hbp : 0 < b := (Real.rpow_pos_of_pos hXp _).trans_le hblo
  have hbκ : X^(1/4:ℝ) ≤ b :=
    (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (1/4:ℝ) ≤ 7/20)).trans hblo
  have hpow : X^(39/100:ℝ) ≤ X^(1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  have hbX : b ≤ X := hbhi.trans (by simpa only [Real.rpow_one] using hpow)
  obtain ⟨hAlo,hAhi⟩ := hr A b hp hp' hblo hbhi
  have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le
    ((le_mul_of_one_le_left (Real.rpow_nonneg hbp.le _) (by norm_num : (1:ℝ) ≤ 2)).trans hAlo)
  have hh := hb (ρ-1) b V A X H hw.1 hw.2.1 hw.2.2 (htwo.trans hbκ) hbκ hbX hXp
    hV (by simpa only [Real.rpow_one] using hVX) hH
    (distinguishedStoppingWeights d) (hweights i N d).1 (hweights i N d).2.1
    (hweights i N d).2.2 hAlo hAhi 1 one_ne_zero
    (by simp only [norm_one_eq,Real.rpow_zero,le_refl]) j q h Z Q early hj
    (by simpa only [show 1+(ρ-1)=ρ by ring] using hrough) E₀ U P primeDetectorCutoff (X^ξ)
    remaining hE₀ (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) hP
  simp only [show 1+(ρ-1)=ρ by ring,angularStoppedAlpha,angularStoppedRowCoefficient] at hh
  rw [centeredHeightSum_angular_factors] at hh
  apply hh.trans
  have hscale : A^(5/6:ℝ)*b^(5/6:ℝ) ≤ (16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ) := by
    rw [←Real.mul_rpow hAp.le hbp.le,←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hXp.le]
    exact Real.rpow_le_rpow (mul_nonneg hAp.le hbp.le) hp' (by norm_num)
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Real.log_pos hX).le _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale hK.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralAngularScaleFirstStoppedEarly
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary cancellation for every actual early stopped dyad. All length,
weight and support conditions are derived from its original finite sum. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem angular_distinguishedStoppedDyad_early_bound_actual (ℓ : ℤ) (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    {C ξ ρ ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100)
    (k Ct : ℕ) :
    ∃ (G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ H : ℝ, 0 < H → ∀ h : ℕ,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ)
        (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h) →
      ∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ) (j r : ℕ), 1 ≤ q.2.1 → q.1 < h →
      ‖angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h true d q j r‖ ≤
        K*X^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨G,K,hK,hbound⟩ := angular_ordinary_stopped_low_kernel_bound_actual ℓ i hpnt hEF hℓ hMV hC
    hHuxley  hGamma hξ hξz hρ hρ₂ k Ct
  refine ⟨G,K,hK,?_⟩
  filter_upwards [hbound,eventually_angular_distinguishedStoppedDyad_geometry ℓ hρ hρ₂ hε hsmall hgap,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 9/25)).eventually_ge_atTop 2,
    eventually_gt_atTop (1:ℝ)] with X hb hg hZ hX
  intro H hH h hh hrough d q j r hk hjh
  have hXp : 0 < X := zero_lt_one.trans hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  by_cases hz : angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h true d q j r = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨hBlo,hBhi,hBX,hABlo,hABhi,hj⟩ := hg i Ct H h true d q j r hk hz
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  have he : geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h =
      geometricBinLower ρ X
        (h-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X)) := by
    simpa only [Nat.sub_add_cancel hh] using
      geometricBinLower_shift hρ hXp hXF
        (h-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X))
  rw [angular_distinguishedStoppedDyad_to_row ℓ i hρ hρ₂ hX.le Ct H h true d q j r hk
    (by simpa only [Bool.true_eq,ite_true, if_true] using hZ) hBX hj hh]
  have hP (n : Eisenstein) (hn : n ∈ stoppedNormDyad (distinguishedStoppedSide X) j) :
      primary n ∧ Squarefree n ∧ stoppedNormDyadLength j/2 ≤ norm n ∧
        norm n ≤ 2*(stoppedNormDyadLength j/2) := by
    have hs := distinguishedStoppedSide_spec (Finset.mem_filter.mp hn).1
    have hh := stoppedNormDyad_outer_bounds hn hs.1
    exact ⟨hs.1,hs.2.1,hh.1,by nlinarith [hh.2]⟩
  have hresult := hb _ d (stoppedNormDyadLength j/2) (stoppedNormDyadLength r) H
    hABlo hABhi hBlo hBhi hH
    (q.1-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X))
    q.2.1 (h-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X))
    (X^(9/25:ℝ)) (X^(9/25:ℝ)) true (by omega)
    (by simpa only [he] using hrough)
    (centralPrimaryFactors X) (centralPrimaryFactors X)
    (stoppedNormDyad (distinguishedStoppedSide X) j)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.2)
    (fun n hn => (mem_primaryElementBall.mp hn).1) hP
  simpa only [distinguishedStoppedAlpha,distinguishedShiftedSideTest,Bool.true_eq,ite_true, if_true]
    using hresult

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralAngularScaleFirstEarlyNegligible
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single logarithmic boundary makes all finitely many early stopped
arities negligible. No boundary is chosen before the analytic constants. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem angular_scaleFirstStoppedEarly_isLittleO_actual_oai (ℓ : ℤ) (m : ℕ)
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    {C ξ ρ ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100)
    (Ct : ℕ) :
    ∃ G : ℕ, ∀ (H : ℝ → ℝ) (h : ℝ → ℕ),
      (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (∀ᶠ X : ℝ in atTop,
        geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X) →
      (∀ᶠ X : ℝ in atTop, 2*(Real.log X)^G ≤ min (X^ξ)
        (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X))) →
      (fun X => angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) true)
        =o[atTop] firstMomentScale := by
  have hdata (i : Fin m) := angular_distinguishedStoppedDyad_early_bound_actual ℓ i.val hpnt hEF hℓ hMV hC
    hHuxley  hGamma hξ hξz hρ hρ₂ hε hsmall hgap (i.val+8) Ct
  choose G K hK hb using hdata
  let G₀ := ∑ i : Fin m, G i
  refine ⟨G₀,?_⟩
  intro H h hH hh hrough
  unfold angular_scaleFirstStoppedSum
  apply Asymptotics.IsLittleO.fun_sum
  intro i hi
  let ii : Fin m := ⟨i,Finset.mem_range.mp hi⟩
  obtain ⟨D,hD,hagg⟩ := angular_distinguishedScaleStopped_bound ℓ i hρ
  have hGG : G ii ≤ G₀ := Finset.single_le_sum (fun j _ => Nat.zero_le (G j)) (Finset.mem_univ ii)
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound (D*K ii*2^(i+8))
  filter_upwards [hb ii,hH,hh,hrough,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with X hbound hH hh hrough hX hlog
  have hKi : 0 < K ii := hK ii
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hL : 0 < 1+Real.log X := by linarith
  have hroughi : 2*(Real.log X)^(G ii) ≤ min (X^ξ)
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X)) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog hGG) (by norm_num)).trans hrough
  have hpiece (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ)
      (hq : q ∈ (if true then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h X) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)))
      (j r : ℕ) :
      ‖angular_distinguishedStoppedDyad ℓ i ρ ξ Ct (H X) X (h X) true d q j r‖ ≤
        K ii*X^(5/6:ℝ)/(Real.log X)^(i+8) := by
    have hq' := Finset.mem_filter.mp hq
    have hk : 1 ≤ q.2.1 := (Finset.mem_filter.mp hq'.1).2
    exact hbound (H X) hH (h X) hh hroughi d q j r hk hq'.2
  have hsum := hagg Ct ξ (H X) X hX (h X) true
    (K ii*X^(5/6:ℝ)/(Real.log X)^(i+8)) (by positivity) hpiece
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
  apply hsum.trans
  have hn := stopped_log_quotient_normalize (i+5) 3 hlog (hK ii).le
    (Real.rpow_nonneg hXp.le (5/6:ℝ))
  have hn' : (1+Real.log X)^(i+5)*(K ii*X^(5/6:ℝ)/(Real.log X)^(i+8)) ≤
      (K ii*2^(i+8))*X^(5/6:ℝ)/(1+Real.log X)^3 := by
    simpa only [show i+5+3=i+8 by omega] using hn
  calc
    _ = D*((1+Real.log X)^(i+5)*(K ii*X^(5/6:ℝ)/(Real.log X)^(i+8))) := by ring
    _ ≤ D*((K ii*2^(i+8))*X^(5/6:ℝ)/(1+Real.log X)^3) :=
      mul_le_mul_of_nonneg_left hn' hD.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual_oai := @OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual_oai
