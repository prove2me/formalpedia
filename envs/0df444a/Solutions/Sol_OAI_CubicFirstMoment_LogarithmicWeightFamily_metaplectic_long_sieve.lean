-- Prove2me | solution 1 for OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:59:44.197508+00:00
-- url     : https://prove2.me/submissions/0c38d96c-b6c8-4fa8-a260-a67a3c304eae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A012
import Definitions.Def_OAIQ096A013
import Definitions.Def_OAIQ096A014
import Definitions.Def_OAIQ096A015
import Theorems.Thm_OAI_CubicFirstMoment_sieveExponent_four_thirds

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_SieveImprovement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification, iteration to exponent four-thirds and the cubic large sieve. -/

section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma small_four_thirds_le_mixed {M N : ℝ} (hN : 0 ≤ N) (hNM : N ≤ M) :
    N^(4/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  calc
    _ = (N*N)^(2/3 : ℝ) := by
      rw [← pow_two,← Real.rpow_natCast_mul hN]
      norm_num
    _ ≤ _ := by gcongr

theorem finiteCubicBound_sharp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ b ∈ H, primary b ∧ Squarefree b ∧ norm b ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^ε*(M+N+(M*N)^(2/3 : ℝ)) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := sieveExponent_four_thirds ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro S H M N hM hN hS hH
  have hM0 : 0 ≤ M := (zero_lt_one.trans_le hM).le
  have hN0 : 0 ≤ N := (zero_lt_one.trans_le hN).le
  have hmixed : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
  rcases le_total N M with hNM | hMN
  · have hs := small_four_thirds_le_mixed hN0 hNM
    have hh : M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ) ≤ 2*(M+N+(M*N)^(2/3 : ℝ)) := by linarith
    exact (hbound S H M N hM hN hS hH).trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))
  · rw [finiteCubicBound_symm S H (fun a ha => (hS a ha).1) (fun b hb => (hH b hb).1)]
    have hs := small_four_thirds_le_mixed hM0 hMN
    rw [mul_comm N M] at hs
    have hh : N+(M*N)^(2/3 : ℝ)+M^(4/3 : ℝ) ≤ 2*(M+N+(M*N)^(2/3 : ℝ)) := by linarith
    have hb := hbound H S N M hN hM hH hS
    rw [mul_comm N M] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMellinProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

/-- For primary factors, fixing the first divisor determines the second. -/
lemma primary_pair_fiber_le_divisors (B : Finset Eisenstein)
    (hB : ∀ a ∈ B, primary a) (n : Eisenstein) :
    ((B.product B).filter (fun z => z.1*z.2 = n)).card ≤
      (B.filter (fun a => a ∣ n)).card := by
  let T := (B.product B).filter (fun z => z.1*z.2 = n)
  have hinj : Set.InjOn Prod.fst (T : Set (Eisenstein × Eisenstein)) := by
    intro a ha b hb he
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply Prod.ext he
    have hn : a.1 ≠ 0 := primary_ne_zero (hB a.1 (Finset.mem_product.mp ha'.1).1)
    apply mul_left_cancel₀ hn
    calc
      a.1*a.2 = n := ha'.2
      _ = b.1*b.2 := hb'.2.symm
      _ = a.1*b.2 := by rw [he]
  have hsub : T.image Prod.fst ⊆ B.filter (fun a => a ∣ n) := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hz).1,?_⟩
    exact ⟨z.2,hzn.symm⟩
  exact (Finset.card_image_iff.mpr hinj).symm.le.trans (Finset.card_le_card hsub)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDivisorPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RamifiedIdealParts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the finitely many primes above three in the
complete ideal lattice. No ramified Euler term is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_mul_pos (u : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    mellinPhase u (x*y) = mellinPhase u x*mellinPhase u y := by
  unfold mellinPhase
  rw [Real.log_mul hx.ne' hy.ne',mul_add,Complex.ofReal_add,add_mul,Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimalFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact support turns the literal completed sum, at every translated
height, into the finite primary cube polynomial used by Montgomery--Vaughan. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticPrimaryPair_injective : Function.Injective metaplecticPrimaryPair := by
  intro du ev h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

lemma metaplecticPrimalSupport_of_nonzero {r : Eisenstein} (ℓ : ℤ)
    (W : ℝ → ℂ) {X B V : ℝ} (hX : 0 < X) (hBV : B*X ≤ V)
    (hW : ∀ x : ℝ, B < x → W x = 0) (du : PrimaryArgument × PrimaryArgument)
    (hn : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) ≠ 0) :
    du ∈ metaplecticPrimalSupport V := by
  have hnW : W (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))/X) ≠ 0 := by
    intro hh
    exact hn (by simp [metaplecticPrimalCoefficient,hh])
  have hsize : norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ V := by
    have hb : norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ B*X := by
      by_contra h
      exact hnW (hW _ ((lt_div_iff₀ hX).mpr (lt_of_not_ge h)))
    exact hb.trans hBV
  have hcube : primary ((du.1:Eisenstein)^3) := by
    simpa only [pow_succ,pow_zero,one_mul] using
      primary_mul (primary_mul du.1.property du.1.property) du.1.property
  have hp : primary (metaplecticCubeProduct (metaplecticPrimaryPair du)) :=
    primary_mul du.2.property hcube
  have hd : (du.1:Eisenstein) ∣ metaplecticCubeProduct (metaplecticPrimaryPair du) :=
    (dvd_pow_self du.1.val (by norm_num : (3:ℕ) ≠ 0)).trans (dvd_mul_left _ _)
  have hu : (du.2:Eisenstein) ∣ metaplecticCubeProduct (metaplecticPrimaryPair du) := dvd_mul_right _ _
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hsize⟩
  · apply Finset.mem_subtype.mpr
    exact mem_primaryElementBall.mpr ⟨du.1.property,(norm_le_of_dvd (primary_ne_zero hp) hd).trans hsize⟩
  · apply Finset.mem_subtype.mpr
    exact mem_primaryElementBall.mpr ⟨du.2.property,(norm_le_of_dvd (primary_ne_zero hp) hu).trans hsize⟩

lemma metaplecticHeightCompleted_zero (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) :
    metaplecticHeightCompleted r ℓ W X 0 = metaplecticCompleted r ℓ W X := by
  unfold metaplecticHeightCompleted metaplecticCompleted
  apply tsum_congr
  intro du
  simp [metaplecticPrimalCoefficient,metaplecticPrimaryPair,metaplecticCubeProduct,mellinPhase]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletedBox
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compactly supported completed sum can be written over a fixed
finite box of primary pairs. This box is independent of the height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_pair_box_image (F : ℝ) :
    (((primaryElementBall F).subtype primary).product
      ((primaryElementBall F).subtype primary)).image metaplecticPrimaryPair =
        (primaryElementBall F).product (primaryElementBall F) := by
  ext du
  constructor
  · intro h
    obtain ⟨ev,hev,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hd,hu⟩ := Finset.mem_product.mp hev
    exact Finset.mem_product.mpr ⟨Finset.mem_subtype.mp hd,Finset.mem_subtype.mp hu⟩
  · intro h
    obtain ⟨hd,hu⟩ := Finset.mem_product.mp h
    refine Finset.mem_image.mpr ⟨(⟨du.1,(mem_primaryElementBall.mp hd).1⟩,
      ⟨du.2,(mem_primaryElementBall.mp hu).1⟩),?_,rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_subtype.mpr hd,Finset.mem_subtype.mpr hu⟩

theorem metaplecticHeightCompleted_box (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {X B F : ℝ} (hX : 0 < X) (hBF : B*X ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t =
      ∑ c ∈ primaryElementBall F, ∑ u ∈ primaryElementBall F,
        metaplecticPrimalCoefficient r ℓ W X (c,u)*
          mellinPhase t (norm (metaplecticCubeProduct (c,u))) := by
  let P := ((primaryElementBall F).subtype primary).product
    ((primaryElementBall F).subtype primary)
  have he : metaplecticHeightCompleted r ℓ W X t =
      ∑ du ∈ P, metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
        mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))) := by
    change (∑' du : PrimaryArgument × PrimaryArgument,
      metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
        mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du)))) = _
    apply tsum_eq_sum
    intro du hdu
    have hc : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) = 0 := by
      by_contra hn
      have hs := metaplecticPrimalSupport_of_nonzero ℓ W hX hBF hW du hn
      exact hdu (Finset.mem_filter.mp hs).1
    rw [hc,zero_mul]
  rw [he,←Finset.sum_product']
  have himage := primary_pair_box_image F
  change P.image metaplecticPrimaryPair = primaryElementBall F ×ˢ primaryElementBall F at himage
  rw [←himage,Finset.sum_image]
  exact fun _ _ _ _ h => metaplecticPrimaryPair_injective h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletionCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed formal coefficients are exactly the actual primary
Gauss cube-divisor coefficients, including the positive angular index
and the height multiplier. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma theta_cube_index (ℓ : ℤ) {c : Eisenstein} (hc : c ≠ 0) :
    theta (3*ℓ) c = theta ℓ (c^3) := by
  rw [show 3*ℓ = (ℓ+ℓ)+ℓ by ring,theta_add (ℓ+ℓ) ℓ hc,theta_add ℓ ℓ hc]
  simp only [pow_succ,pow_zero,one_mul,theta_mul]

lemma mellinPhase_cube_norm (t : ℝ) (x : ℝ) :
    mellinPhase (3*t) x = mellinPhase t (x^3) := by
  unfold mellinPhase
  rw [Real.log_pow]
  congr 1
  push_cast
  ring

lemma metaplecticCompletionWeight_phase (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    metaplecticCompletionWeight r ℓ t c =
      if IsCoprime c r then
        (Real.sqrt (norm c):ℂ)*theta ℓ (c^3)*mellinPhase t (norm c^3)
      else 0 := by
  unfold metaplecticCompletionWeight
  rw [theta_cube_index ℓ (primary_ne_zero hc),
    ←mellinPhase_eq_cpow (norm_pos_of_ne_zero (primary_ne_zero hc)) (3*t),
    mellinPhase_cube_norm]

lemma metaplectic_completion_factor (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c u : Eisenstein} (hc : primary c) (hu : primary u) :
    metaplecticCompletionWeight r ℓ t c*
      (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u)) =
        metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (c,u)*
          mellinPhase t (norm (metaplecticCubeProduct (c,u))) := by
  rw [metaplecticCompletionWeight_phase r ℓ t hc]
  by_cases hcr : IsCoprime c r
  · simp only [hcr,ite_true, if_true,metaplecticPrimalCoefficient,metaplecticCubeProduct,
      mul_one,theta_mul,norm_mul_eq,eisenstein_norm_pow]
    rw [mellinPhase_mul_pos t (norm_pos_of_ne_zero (primary_ne_zero hu))
      (pow_pos (norm_pos_of_ne_zero (primary_ne_zero hc)) 3)]
    ring
  · simp [hcr,metaplecticPrimalCoefficient]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletedPolynomial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the completed ideal polynomial with the
original completed Gauss sum at every real height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_primal_weight_factor (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (X t : ℝ) (c u : Eisenstein) :
    W (norm (c^3*u)/X)*(metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (c,u)*
      mellinPhase t (norm (metaplecticCubeProduct (c,u)))) =
        metaplecticPrimalCoefficient r ℓ W X (c,u)*
          mellinPhase t (norm (metaplecticCubeProduct (c,u))) := by
  by_cases hcr : IsCoprime c r
  · simp only [metaplecticPrimalCoefficient,hcr,ite_true, if_true,mul_one,
      metaplecticCubeProduct]
    rw [show c^3*u = u*c^3 by ring]
    ring
  · simp [metaplecticPrimalCoefficient,hcr]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticActualInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inverse completion for the original angular, norm-twisted
smooth Gauss sum. All cube-divisor sums are finite by the actual support
of the weight, and the rescaled completed length is retained literally. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticAngularSmoothSum_finite (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticAngularSmoothSum r ℓ W U t =
      ∑ u ∈ primaryElementBall F,
        W (norm u/U)*(gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u)) := by
  let S := (primaryElementBall F).subtype primary
  have he : metaplecticAngularSmoothSum r ℓ W U t =
      ∑ u ∈ S, (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))*W (norm u/U) := by
    apply tsum_eq_sum
    intro u hu
    have hnorm : F < norm u := by
      by_contra hn
      exact hu (Finset.mem_subtype.mpr (mem_primaryElementBall.mpr ⟨u.property,le_of_not_gt hn⟩))
    rw [hW _ ((lt_div_iff₀ hU).mpr (hBF.trans_lt hnorm)),mul_zero]
  rw [he]
  dsimp only [S]
  rw [Finset.sum_subtype_of_mem
    (fun u : Eisenstein => (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))*W (norm u/U))
    (fun _ hu => (mem_primaryElementBall.mp hu).1)]
  apply Finset.sum_congr rfl
  intro u _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual bilinear Gauss kernel is controlled by the proved cubic
large sieve. This is the finite arithmetic step in the long Type-I tail. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_bilinear_factor (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hA : ∀ r ∈ A, primary r) (hB : ∀ u ∈ B, primary u) :
    (∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)) =
      ∑ r ∈ A, (α r*gauss r)*
        ∑ u ∈ B, (β u*gauss u)*star (cubicSymbol u r) := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [gauss_mul (hA r hr) (hB u hu)]
  ring

lemma gauss_weight_energy (A : Finset Eisenstein) (α : Eisenstein → ℂ)
    (hA : ∀ r ∈ A, primary r) :
    (∑ r ∈ A, ‖α r*gauss r‖^2) ≤ ∑ r ∈ A, ‖α r‖^2 := by
  apply Finset.sum_le_sum
  intro r hr
  rw [norm_mul]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_gauss_le_one (hA r hr))) 2

lemma metaplectic_bilinear_operator (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hA : ∀ r ∈ A, primary r) (hB : ∀ u ∈ B, primary u) :
    ‖∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)‖^2 ≤
      finiteCubicBound B A*(∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2) := by
  have he (r : Eisenstein) :
      (∑ u ∈ B, (β u*gauss u)*star (cubicSymbol u r)) =
        star (∑ u ∈ B, star (β u*gauss u)*cubicSymbol u r) := by
    simp only [star_sum,star_mul,star_star,mul_comm]
  have hrows : (∑ r ∈ A, ‖∑ u ∈ B, (β u*gauss u)*star (cubicSymbol u r)‖^2) ≤
      finiteCubicBound B A*(∑ u ∈ B, ‖β u‖^2) := by
    simp_rw [he,norm_star]
    exact (finiteCubicBound_controls_mass B A (fun u => star (β u*gauss u))).trans
      (mul_le_mul_of_nonneg_left (by
        simpa only [norm_star] using gauss_weight_energy B β hB)
        (finiteCubicBound_nonneg _ _))
  rw [metaplectic_bilinear_factor A B α β hA hB]
  apply (complex_bilinear_rows_sq A (fun r => α r*gauss r)
    (fun r => ∑ u ∈ B, (β u*gauss u)*star (cubicSymbol u r))).trans
  have h := mul_le_mul (gauss_weight_energy A α hA) hrows
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact h.trans_eq (by ring)

theorem metaplectic_bilinear_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : Finset Eisenstein) (R V : ℝ), 1 ≤ R → 1 ≤ V →
      (∀ r ∈ A, primary r ∧ Squarefree r ∧ norm r ≤ R) →
      (∀ u ∈ B, primary u ∧ Squarefree u ∧ norm u ≤ V) →
      ∀ α β : Eisenstein → ℂ,
      ‖∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)‖^2 ≤
        C*(R*V)^ε*(R+V+(R*V)^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2) := by
  obtain ⟨C,hC,hbound⟩ := finiteCubicBound_sharp ε hε
  refine ⟨C,hC,?_⟩
  intro A B R V hR hV hA hB α β
  apply (metaplectic_bilinear_operator A B α β (fun r hr => (hA r hr).1)
    (fun u hu => (hB u hu).1)).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound B A R V hR hV hB hA)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBilinearMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem metaplectic_bilinear_mellin (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : Eisenstein → ℝ → ℂ)
    (hW : ∀ r ∈ A, HasCompactSupport (W r))
    (hpos : ∀ r ∈ A, tsupport (W r) ⊆ Set.Ioi 0)
    (hsm : ∀ r ∈ A, ContDiff ℝ ∞ (W r))
    (hB : ∀ u ∈ B, primary u) {V : ℝ} (hV : 0 < V) :
    (∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)*W r (norm u/V)) =
      ∫ t : ℝ, ∑ r ∈ A, ∑ u ∈ B,
        (α r*zeroLineMellinWeight (W r) V t)*
          (β u*mellinPhase (-t) (norm u))*gauss (r*u) := by
  let f (r u : Eisenstein) (t : ℝ) : ℂ :=
    zeroLineMellinWeight (W r) V t*((α r*β u*gauss (r*u))*mellinPhase (-t) (norm u))
  have hi (r : Eisenstein) (hr : r ∈ A) (u : Eisenstein) (hu : u ∈ B) :
      Integrable (f r u) := metaplectic_mellin_term_integrable (W r)
    (hW r hr) (hpos r hr) (hsm r hr) hV
    (norm_pos_of_ne_zero (primary_ne_zero (hB u hu))) _
  calc
    _ = ∑ r ∈ A, ∑ u ∈ B, ∫ t : ℝ, f r u t := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro u hu
      exact metaplectic_mellin_term (W r) (hW r hr) (hpos r hr) (hsm r hr) hV
        (norm_pos_of_ne_zero (primary_ne_zero (hB u hu))) _
    _ = ∫ t : ℝ, ∑ r ∈ A, ∑ u ∈ B, f r u t := by
      rw [integral_finsetSum A (fun r hr => integrable_finsetSum B (hi r hr))]
      apply Finset.sum_congr rfl
      intro r hr
      exact (integral_finsetSum B (hi r hr)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro u _
      dsimp [f]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticForwardCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact forward completion over a finite primary box. This identity
allows the long inverse divisors to be collected by their actual product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_forward_completion (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticCompleted r ℓ W U =
      ∑ d ∈ primaryElementBall F, metaplecticCompletionWeight r ℓ 0 d*
        metaplecticAngularSmoothSum r ℓ W (U/norm d^3) 0 := by
  rw [←metaplecticHeightCompleted_zero r ℓ W U,
    metaplecticHeightCompleted_box r ℓ W hU hBF hW 0]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp := (mem_primaryElementBall.mp hd).1
  have hNd : 0 < norm d := norm_pos_of_ne_zero (primary_ne_zero hdp)
  have hV : 0 < U/norm d^3 := div_pos hU (pow_pos hNd 3)
  have hVU : U/norm d^3 ≤ U := div_le_self hU.le
    (one_le_pow₀ (one_le_norm (primary_ne_zero hdp)))
  have hBV : B*(U/norm d^3) ≤ F := (mul_le_mul_of_nonneg_left hVU hB).trans hBF
  rw [metaplecticAngularSmoothSum_finite r ℓ W hV hBV hW 0,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hup := (mem_primaryElementBall.mp hu).1
  have hf := metaplectic_completion_factor r ℓ 0 hdp hup
  have hw := metaplectic_primal_weight_factor r ℓ W U 0 d u
  simp only [mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one] at hf hw ⊢
  have hn : norm (d^3*u)/U = norm u/(U/norm d^3) := by
    rw [norm_mul_eq,eisenstein_norm_pow]
    field_simp
  rw [hn,←hf] at hw
  rw [←hw]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticWeightedBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic-sieve bound for the actual varying-weight bilinear Gauss
sum. The common Mellin majorant is derived from the given weight family. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma UniformLogWeights.zeroLine_majorant
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r : γ) (V : ℝ), 0 < V → ∀ t : ℝ,
      ‖zeroLineMellinWeight (W r) V t‖ ≤
        (1/(2*Real.pi))*mellinEdgeMajorant D t := by
  obtain ⟨D,hD,hdecay⟩ := hW.mellin_decay 0 2
  refine ⟨D,hD,?_⟩
  intro r V hV t
  rw [zeroLineMellinWeight_norm (W r) hV]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (le_div_iff₀ (by positivity : 0 < (1+|t|)^2)).mpr
  exact (mul_comm _ _).trans_le (by simpa using hdecay r 0 (by norm_num) t)

theorem UniformLogWeights.metaplectic_weighted_bilinear
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A B : Finset Eisenstein) (N Z V : ℝ),
      1 ≤ N → 1 ≤ Z → 0 < V →
      (∀ r ∈ A, primary r ∧ Squarefree r ∧ norm r ≤ N) →
      (∀ u ∈ B, primary u ∧ Squarefree u ∧ norm u ≤ Z) →
      ∀ α β : Eisenstein → ℂ,
      ‖∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)*W (w r) (norm u/V)‖^2 ≤
        K*(N*Z)^ε*(N+Z+(N*Z)^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2) := by
  obtain ⟨C,hC,hbilinear⟩ := metaplectic_bilinear_sieve hε
  obtain ⟨D,hD,hmajorant⟩ := hW.zeroLine_majorant
  let m : ℝ → ℝ := fun t => (1/(2*Real.pi))*mellinEdgeMajorant D t
  have hm : Integrable m := (mellinEdgeMajorant_integrable D).const_mul _
  have hm0 (t : ℝ) : 0 ≤ m t := by dsimp [m,mellinEdgeMajorant]; positivity
  let H : ℝ := ∫ t : ℝ, m t
  have hH : 0 ≤ H := integral_nonneg hm0
  refine ⟨(1+H)^2*C,by positivity,?_⟩
  intro w A B N Z V hN hZ hV hA hB α β
  let Q : ℝ := C*(N*Z)^ε*(N+Z+(N*Z)^(2/3:ℝ))*
    (∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let F : ℝ → ℂ := fun t => ∑ r ∈ A, ∑ u ∈ B,
    (α r*zeroLineMellinWeight (W (w r)) V t)*
      (β u*mellinPhase (-t) (norm u))*gauss (r*u)
  have hb (t : ℝ) : ‖F t‖^2 ≤ (m t)^2*Q := by
    have hα : (∑ r ∈ A, ‖α r*zeroLineMellinWeight (W (w r)) V t‖^2) ≤
        (m t)^2*(∑ r ∈ A, ‖α r‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul,mul_pow]
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (_root_.norm_nonneg _) (hmajorant (w r) V hV t) 2)
        (sq_nonneg _)).trans_eq (mul_comm _ _)
    have hβ : (∑ u ∈ B, ‖β u*mellinPhase (-t) (norm u)‖^2) =
        ∑ u ∈ B, ‖β u‖^2 := by
      apply Finset.sum_congr rfl
      intro u _
      simp [mellinPhase,Complex.norm_exp]
    have h := hbilinear A B N Z hN hZ hA hB
      (fun r => α r*zeroLineMellinWeight (W (w r)) V t)
      (fun u => β u*mellinPhase (-t) (norm u))
    rw [hβ] at h
    apply h.trans
    calc
      _ ≤ C*(N*Z)^ε*(N+Z+(N*Z)^(2/3:ℝ))*
          ((m t)^2*(∑ r ∈ A, ‖α r‖^2))*(∑ u ∈ B, ‖β u‖^2) := by gcongr
      _ = _ := by dsimp [Q]; ring
  have hn (t : ℝ) : ‖F t‖ ≤ m t*Real.sqrt Q := by
    have h := Real.le_sqrt_of_sq_le (hb t)
    rwa [Real.sqrt_mul (sq_nonneg (m t)),Real.sqrt_sq_eq_abs,
      abs_of_nonneg (hm0 t)] at h
  have hnorm : ‖∫ t : ℝ, F t‖ ≤ H*Real.sqrt Q := by
    have hi := norm_integral_le_of_norm_le (hm.mul_const (Real.sqrt Q))
      (Filter.Eventually.of_forall hn)
    simpa only [integral_mul_const] using hi
  rw [metaplectic_bilinear_mellin A B α β (fun r => W (w r))
    (fun r _ => hW.compact (w r)) (fun r _ => hW.positive (w r))
    (fun r _ => hW.smooth (w r)) (fun u hu => (hB u hu).1) hV]
  change ‖∫ t : ℝ, F t‖^2 ≤ _
  calc
    _ ≤ (H*Real.sqrt Q)^2 := pow_le_pow_left₀ (_root_.norm_nonneg _) hnorm 2
    _ = H^2*Q := by rw [mul_pow,Real.sq_sqrt hQ]
    _ ≤ (1+H)^2*Q := mul_le_mul_of_nonneg_right (by nlinarith) hQ
    _ = _ := by dsimp [Q]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSquarefreeBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Automatic squarefree support for the actual bilinear Gauss sum.
No squarefree restriction is imposed on its original coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_bilinear_squarefree (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : Eisenstein → ℝ → ℂ) (V : ℝ)
    (hA : ∀ r ∈ A, primary r) (hB : ∀ u ∈ B, primary u) :
    (∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)*W r (norm u/V)) =
      ∑ r ∈ A.filter Squarefree, ∑ u ∈ B.filter Squarefree,
        α r*β u*gauss (r*u)*W r (norm u/V) := by
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hs : Squarefree r
  · rw [ite_eq_left hs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases ht : Squarefree u
    · rw [ite_eq_left ht]
    · rw [ite_eq_right ht,gauss_eq_zero_of_not_squarefree (primary_mul (hA r hr) (hB u hu))
        (fun h => ht (Squarefree.squarefree_of_dvd (dvd_mul_left u r) h))]
      ring
  · rw [ite_eq_right hs]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    rw [gauss_eq_zero_of_not_squarefree (primary_mul (hA r hr) (hB u hu))
      (fun h => hs (Squarefree.squarefree_of_dvd (dvd_mul_right r u) h))]
    ring

theorem UniformLogWeights.metaplectic_unrestricted_bilinear
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A B : Finset Eisenstein) (N Z V : ℝ),
      1 ≤ N → 1 ≤ Z → 0 < V →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ u ∈ B, primary u ∧ norm u ≤ Z) →
      ∀ α β : Eisenstein → ℂ,
      ‖∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)*W (w r) (norm u/V)‖^2 ≤
        K*(N*Z)^ε*(N+Z+(N*Z)^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_weighted_bilinear hε
  refine ⟨K,hK,?_⟩
  intro w A B N Z V hN hZ hV hA hB α β
  rw [metaplectic_bilinear_squarefree A B α β (fun r => W (w r)) V
    (fun r hr => (hA r hr).1) (fun u hu => (hB u hu).1)]
  apply (hbound w (A.filter Squarefree) (B.filter Squarefree) N Z V hN hZ hV
    (fun r hr => ⟨(hA r (Finset.mem_filter.mp hr).1).1,(Finset.mem_filter.mp hr).2,
      (hA r (Finset.mem_filter.mp hr).1).2⟩)
    (fun u hu => ⟨(hB u (Finset.mem_filter.mp hu).1).1,(Finset.mem_filter.mp hu).2,
      (hB u (Finset.mem_filter.mp hu).1).2⟩) α β).trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  · positivity
  · positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSmoothBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic-sieve bound applied to the original smooth angular Gauss
sums, with the actual compact support and coefficient energies. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_angular_bilinear_identity (A : Finset Eisenstein)
    (α : Eisenstein → ℂ) (W : Eisenstein → ℝ → ℂ) (ℓ : ℤ)
    {U B : ℝ} (hU : 0 < U) (hcut : ∀ r ∈ A, ∀ x : ℝ, B < x → W r x = 0) :
    (∑ r ∈ A, α r*metaplecticAngularSmoothSum r ℓ (W r) U 0) =
      ∑ r ∈ A, ∑ u ∈ primaryElementBall (B*U),
        (α r*theta ℓ r)*theta ℓ u*gauss (r*u)*W r (norm u/U) := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [metaplecticAngularSmoothSum_finite r ℓ (W r) hU (le_refl (B*U)) (hcut r hr) 0,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [theta_mul]
  simp only [mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one]
  ring

theorem UniformLogWeights.metaplectic_smooth_bilinear
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein) (N U B : ℝ),
      1 ≤ N → 0 < U → 1 ≤ B*U →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ r ∈ A, α r*metaplecticAngularSmoothSum r ℓ (W (w r)) U 0‖^2 ≤
        K*(N*(B*U))^ε*(B*U)*(N+B*U+(N*(B*U))^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_unrestricted_bilinear hε
  refine ⟨18*K,by positivity,?_⟩
  intro w A N U B hN hU hBU hA hcut α ℓ
  rw [metaplectic_angular_bilinear_identity A α (fun r => W (w r)) ℓ hU hcut]
  have heα : (∑ r ∈ A, ‖α r*theta ℓ r‖^2) = ∑ r ∈ A, ‖α r‖^2 := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [norm_mul,norm_theta (primary_ne_zero (hA r hr).1),mul_one]
  have heβ : (∑ u ∈ primaryElementBall (B*U), ‖theta ℓ u‖^2) =
      ((primaryElementBall (B*U)).card:ℝ) := by
    calc
      _ = ∑ _u ∈ primaryElementBall (B*U), (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [norm_theta (primary_ne_zero (mem_primaryElementBall.mp hu).1),one_pow]
      _ = _ := by simp
  have hb := hbound w A (primaryElementBall (B*U)) N (B*U) U hN hBU hU hA
    (fun u hu => mem_primaryElementBall.mp hu) (fun r => α r*theta ℓ r) (theta ℓ)
  rw [heα,heβ] at hb
  apply hb.trans
  calc
    _ ≤ K*(N*(B*U))^ε*(N+B*U+(N*(B*U))^(2/3:ℝ))*
        (∑ r ∈ A, ‖α r‖^2)*(18*(B*U)) := by
      apply mul_le_mul_of_nonneg_left
        (primaryElementBall_card_le (zero_lt_one.trans_le hBU).le)
      positivity
    _ = _ := by ring

lemma metaplecticAngularSmoothSum_small (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B : ℝ} (hU : 0 < U) (hBU : B*U < 1)
    (hcut : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticAngularSmoothSum r ℓ W U 0 = 0 := by
  rw [metaplecticAngularSmoothSum_finite r ℓ W hU (le_refl (B*U)) hcut 0]
  apply Finset.sum_eq_zero
  intro u hu
  have hn := one_le_norm (primary_ne_zero (mem_primaryElementBall.mp hu).1)
  exact False.elim ((not_lt_of_ge hn) ((mem_primaryElementBall.mp hu).2.trans_lt hBU))

theorem UniformLogWeights.metaplectic_smooth_bilinear_all_lengths
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein) (N U B : ℝ),
      1 ≤ N → 0 < U → 0 ≤ B →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ r ∈ A, α r*metaplecticAngularSmoothSum r ℓ (W (w r)) U 0‖^2 ≤
        K*(N*(B*U))^ε*(B*U)*(N+B*U+(N*(B*U))^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_smooth_bilinear hε
  refine ⟨K,hK,?_⟩
  intro w A N U B hN hU hB hA hcut α ℓ
  by_cases hBU : 1 ≤ B*U
  · exact hbound w A N U B hN hU hBU hA hcut α ℓ
  · have hz : (∑ r ∈ A, α r*metaplecticAngularSmoothSum r ℓ (W (w r)) U 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [metaplecticAngularSmoothSum_small r ℓ (W (w r)) hU (lt_of_not_ge hBU) (hcut r hr),mul_zero]
    rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal grouped coefficient in the long inverse-completion tail.
Its angular and coprimality phases are retained, while the remaining
Möbius divisor sum is bounded by a proved small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticTailCoefficient_factor (r : Eisenstein) (ℓ : ℤ) (C F : ℝ)
    (e : Eisenstein) :
    metaplecticTailCoefficient r ℓ C F e =
      metaplecticCompletionWeight r ℓ 0 e*metaplecticTailMoebius C F e := by
  unfold metaplecticTailCoefficient metaplecticTailMoebius
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro cd hcd
  obtain ⟨hmem,he⟩ := Finset.mem_filter.mp hcd
  have hc := (mem_primaryElementBall.mp (Finset.mem_product.mp hmem).1).1
  have hd := (mem_primaryElementBall.mp (Finset.mem_product.mp hmem).2).1
  by_cases hn : C < norm cd.1
  · simp only [hn,ite_true, if_true]
    rw [←he,metaplecticCompletionWeight_mul r ℓ 0 hc hd]
    ring
  · simp only [hn,ite_false, if_false,mul_zero]

/-- Exact collection of the two actual completion divisors into their
product, for any remaining norm-weighted Gauss sum. -/
theorem metaplecticTailCoefficient_collect (r : Eisenstein) (ℓ : ℤ) (C F : ℝ)
    (g : Eisenstein → ℂ) :
    (∑ c ∈ primaryElementBall F, ∑ d ∈ primaryElementBall F,
      (if C < norm c then (idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c*
        metaplecticCompletionWeight r ℓ 0 d else 0)*g (c*d)) =
      ∑ e ∈ ((primaryElementBall F).product (primaryElementBall F)).image
        (fun cd => cd.1*cd.2), metaplecticTailCoefficient r ℓ C F e*g e := by
  let P := (primaryElementBall F).product (primaryElementBall F)
  let f : Eisenstein × Eisenstein → ℂ := fun cd =>
    (if C < norm cd.1 then (idealMoebius cd.1:ℂ)*metaplecticCompletionWeight r ℓ 0 cd.1*
      metaplecticCompletionWeight r ℓ 0 cd.2 else 0)*g (cd.1*cd.2)
  rw [←Finset.sum_product']
  change (∑ cd ∈ P, f cd) = _
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun cd hcd => Finset.mem_image_of_mem (fun cd : Eisenstein × Eisenstein => cd.1*cd.2) hcd) f]
  apply Finset.sum_congr rfl
  intro e _
  rw [metaplecticTailCoefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro cd hcd
  dsimp only [f]
  rw [(Finset.mem_filter.mp hcd).2]

lemma metaplecticTailMoebius_zero {e : Eisenstein} (he : primary e) {C F : ℝ}
    (hC : norm e ≤ C) : metaplecticTailMoebius C F e = 0 := by
  apply Finset.sum_eq_zero
  intro cd hcd
  have hd := (Finset.mem_filter.mp hcd).2
  have hn : norm cd.1 ≤ norm e := norm_le_of_dvd (primary_ne_zero he) ⟨cd.2,hd.symm⟩
  exact ite_eq_right (not_lt_of_ge (hn.trans hC))

lemma metaplecticTailCoefficient_zero (r : Eisenstein) (ℓ : ℤ)
    {e : Eisenstein} (he : primary e) {C F : ℝ} (hC : norm e ≤ C) :
    metaplecticTailCoefficient r ℓ C F e = 0 := by
  rw [metaplecticTailCoefficient_factor,metaplecticTailMoebius_zero he hC,mul_zero]

theorem metaplecticTailMoebius_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (C F : ℝ) (e : Eisenstein), primary e →
      ‖metaplecticTailMoebius C F e‖ ≤ D*norm e^ε := by
  obtain ⟨D,hD,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨D,hD,?_⟩
  intro C F e he
  have hp (c : Eisenstein) (hc : c ∈ primaryElementBall F) : primary c :=
    (mem_primaryElementBall.mp hc).1
  have hcard : ((metaplecticTailPairs F e).card:ℝ) ≤ D*norm e^ε :=
    (Nat.cast_le.mpr (primary_pair_fiber_le_divisors _ hp e)).trans
      (hdiv _ hp e (primary_ne_zero he))
  unfold metaplecticTailMoebius
  calc
    _ ≤ ∑ cd ∈ metaplecticTailPairs F e,
        ‖if C < norm cd.1 then (idealMoebius cd.1:ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _cd ∈ metaplecticTailPairs F e, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro cd _
      split_ifs
      · exact norm_idealMoebius_le_one _
      · simp
    _ = ((metaplecticTailPairs F e).card:ℝ) := by simp
    _ ≤ _ := hcard

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailLevel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long completion coefficient separates exactly into one fixed
factor and a coprimality restriction on the original outer coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_tail_level_factor (A : Finset Eisenstein) (α : Eisenstein → ℂ)
    (ℓ : ℤ) (C F : ℝ) (e : Eisenstein) (f : Eisenstein → ℂ) :
    (∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*f r) =
      metaplecticTailScalar ℓ C F e*(∑ r ∈ A, metaplecticTailOuter e α r*f r) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [metaplecticTailCoefficient_factor]
  unfold metaplecticTailScalar metaplecticTailOuter metaplecticCompletionWeight
  by_cases hc : IsCoprime e r
  · simp only [hc,ite_true, if_true,mul_zero,Complex.ofReal_zero,zero_mul,Complex.cpow_zero,mul_one]
    ring
  · simp only [hc,ite_false, if_false,zero_mul,mul_zero]

lemma metaplecticTailOuter_energy_le (A : Finset Eisenstein) (e : Eisenstein)
    (α : Eisenstein → ℂ) :
    (∑ r ∈ A, ‖metaplecticTailOuter e α r‖^2) ≤ ∑ r ∈ A, ‖α r‖^2 := by
  apply Finset.sum_le_sum
  intro r _
  unfold metaplecticTailOuter
  split_ifs
  · exact le_rfl
  · simp only [norm_zero,zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

theorem metaplecticTailScalar_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ℓ : ℤ) (C F : ℝ) (e : Eisenstein), primary e →
      ‖metaplecticTailScalar ℓ C F e‖ ≤ D*norm e^(1/2+δ) := by
  obtain ⟨D,hD,hbound⟩ := metaplecticTailMoebius_bound hδ
  refine ⟨D,hD,?_⟩
  intro ℓ C F e he
  rw [metaplecticTailScalar,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),norm_theta (primary_ne_zero he),mul_one]
  calc
    _ ≤ Real.sqrt (norm e)*(D*norm e^δ) :=
      mul_le_mul_of_nonneg_left (hbound C F e he) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,Real.rpow_add (norm_pos_of_ne_zero (primary_ne_zero he))]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic-sieve estimate for the literal fixed-e long completion
term, including its coprimality restriction and every angular phase. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_tail_level_sieve
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein) (N U B C F : ℝ),
      1 ≤ N → 0 < U → 0 ≤ B →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ) (e : Eisenstein), primary e →
      ‖∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0‖^2 ≤
        K*norm e^(1+2*ε)*(N*(B*(U/norm e^3)))^ε*(B*(U/norm e^3))*
          (N+B*(U/norm e^3)+(N*(B*(U/norm e^3)))^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_smooth_bilinear_all_lengths hε
  obtain ⟨D,hD,hscalar⟩ := metaplecticTailScalar_bound hε
  refine ⟨D^2*K,by positivity,?_⟩
  intro w A N U B C F hN hU hB hA hcut α ℓ e he
  have hn : 0 < norm e := norm_pos_of_ne_zero (primary_ne_zero he)
  let V := U/norm e^3
  have hV : 0 < V := div_pos hU (pow_pos hn 3)
  have hs := hbound w A N V B hN hV hB hA hcut (metaplecticTailOuter e α) ℓ
  have hs' : ‖∑ r ∈ A, metaplecticTailOuter e α r*
      metaplecticAngularSmoothSum r ℓ (W (w r)) V 0‖^2 ≤
      K*(N*(B*V))^ε*(B*V)*(N+B*V+(N*(B*V))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) :=
    hs.trans (mul_le_mul_of_nonneg_left (metaplecticTailOuter_energy_le A e α) (by positivity))
  rw [metaplectic_tail_level_factor A α ℓ C F e
    (fun r => metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0),norm_mul,mul_pow]
  calc
    _ ≤ (D*norm e^(1/2+ε))^2*
        (K*(N*(B*V))^ε*(B*V)*(N+B*V+(N*(B*V))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2)) :=
      mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _) (hscalar ℓ C F e he) 2) hs'
        (sq_nonneg _) (sq_nonneg _)
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hn.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (1/2+ε)*(2:ℝ) = 1+2*ε by ring]
      dsimp [V]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongSieveScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact cube-length scaling in the long Type-I sieve bound. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_long_cube_scale {n E V ε : ℝ}
    (hE : 0 < E) (hEn : E ≤ n) (hV : 0 ≤ V) (hε : ε ≤ 1) :
    n^(1+2*ε)*(V/n^3) ≤ V*E^(-2+2*ε) := by
  have hn : 0 < n := hE.trans_le hEn
  have he : n^(1+2*ε)/n^3 = n^(-2+2*ε) := by
    rw [←Real.rpow_natCast n 3,←Real.rpow_sub hn]
    congr 1
    ring
  calc
    _ = V*(n^(1+2*ε)/n^3) := by ring
    _ = V*n^(-2+2*ε) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hE hEn (by linarith)) hV

lemma metaplectic_long_sieve_scale {n E N U B ε : ℝ}
    (hE : 1 ≤ E) (hEn : E ≤ n) (hN : 0 ≤ N) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1) :
    n^(1+2*ε)*(N*(B*(U/n^3)))^ε*(B*(U/n^3))*
        (N+B*(U/n^3)+(N*(B*(U/n^3)))^(2/3:ℝ)) ≤
      (N*(B*U))^ε*(B*U)*E^(-2+2*ε)*
        (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ)) := by
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hn : 0 < n := hEp.trans_le hEn
  have hn1 : 1 ≤ n := hE.trans hEn
  have hz0 : 0 ≤ B*(U/n^3) := by positivity
  have hze0 : 0 ≤ B*(U/E^3) := by positivity
  have hz : B*(U/n^3) ≤ B*U := mul_le_mul_of_nonneg_left
    (div_le_self hU (one_le_pow₀ hn1)) hB
  have hze : B*(U/n^3) ≤ B*(U/E^3) := by
    apply mul_le_mul_of_nonneg_left _ hB
    exact div_le_div_of_nonneg_left hU (pow_pos hEp 3)
      (pow_le_pow_left₀ hEp.le hEn 3)
  have hp : (N*(B*(U/n^3)))^ε ≤ (N*(B*U))^ε :=
    Real.rpow_le_rpow (mul_nonneg hN hz0) (mul_le_mul_of_nonneg_left hz hN) hε
  have hs : N+B*(U/n^3)+(N*(B*(U/n^3)))^(2/3:ℝ) ≤
      N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ) := by
    gcongr
  have hc : n^(1+2*ε)*(B*(U/n^3)) ≤ (B*U)*E^(-2+2*ε) := by
    simpa only [mul_div_assoc] using metaplectic_long_cube_scale hEp hEn
      (mul_nonneg hB hU) hεsmall
  calc
    _ = (n^(1+2*ε)*(B*(U/n^3)))*(N*(B*(U/n^3)))^ε*
        (N+B*(U/n^3)+(N*(B*(U/n^3)))^(2/3:ℝ)) := by ring
    _ ≤ ((B*U)*E^(-2+2*ε))*(N*(B*U))^ε*
        (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ)) :=
      mul_le_mul (mul_le_mul hc hp (by positivity) (by positivity)) hs
        (by positivity) (by positivity)
    _ = _ := by ring

lemma metaplectic_long_dyad_scale {E ε : ℝ} (hE : 0 < E) :
    (36*E)^2*E^(-2+2*ε) = 1296*E^(2*ε) := by
  rw [mul_pow,show (36:ℝ)^2 = 1296 by norm_num,←Real.rpow_two E,
    mul_assoc,←Real.rpow_add hE]
  rw [show (2:ℝ)+(-2+2*ε) = 2*ε by ring]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailDyad
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual long-completion dyad obeys the cubic-sieve estimate.
This theorem retains the original outer coefficients and all e-dependent
coprimality restrictions instead of bounding them by an abstract family. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_tail_dyad_sieve
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A S : Finset Eisenstein) (N U B C F E : ℝ),
      1 ≤ N → 0 < U → 0 ≤ B → 1 ≤ E →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ e ∈ S, primary e ∧ E ≤ norm e ∧ norm e ≤ 2*E) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ e ∈ S, ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0‖^2 ≤
        K*(N*(B*U))^ε*(B*U)*E^(2*ε)*
          (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_tail_level_sieve hε
  refine ⟨1296*K,by positivity,?_⟩
  intro w A S N U B C F E hN hU hB hE hA hS hcut α ℓ
  have hEp : 0 < E := zero_lt_one.trans_le hE
  let M : ℝ := K*(N*(B*U))^ε*(B*U)*E^(-2+2*ε)*
    (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let f : Eisenstein → ℂ := fun e => ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
    metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0
  have hb (e : Eisenstein) (he : e ∈ S) : ‖f e‖^2 ≤ M := by
    apply (hbound w A N U B C F hN hU hB hA hcut α ℓ e (hS e he).1).trans
    have hs := metaplectic_long_sieve_scale hE (hS e he).2.1
      (zero_lt_one.trans_le hN).le hU.le hB hε.le hεsmall
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hK.le)
      (Finset.sum_nonneg (fun r (_ : r ∈ A) => sq_nonneg ‖α r‖))
    simpa only [M,mul_assoc] using hh
  have hcard : (S.card:ℝ) ≤ 36*E := by
    have hs : S ⊆ primaryElementBall (2*E) := by
      intro e he
      exact mem_primaryElementBall.mpr ⟨(hS e he).1,(hS e he).2.2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans
      ((primaryElementBall_card_le (by positivity)).trans_eq (by ring))
  have hCS : ‖∑ e ∈ S, f e‖^2 ≤ (S.card:ℝ)*(∑ e ∈ S, ‖f e‖^2) := by
    simpa using complex_bilinear_rows_sq S (fun _ => (1:ℂ)) f
  change ‖∑ e ∈ S, f e‖^2 ≤ _
  calc
    _ ≤ (S.card:ℝ)*(∑ e ∈ S, ‖f e‖^2) := hCS
    _ ≤ (S.card:ℝ)*(∑ _e ∈ S, M) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum hb) (Nat.cast_nonneg _)
    _ = (S.card:ℝ)^2*M := by simp; ring
    _ ≤ (36*E)^2*M := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hM
    _ = _ := by
      calc
        _ = K*(N*(B*U))^ε*(B*U)*((36*E)^2*E^(-2+2*ε))*
            (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) := by
          dsimp [M]
          ring
        _ = _ := by rw [metaplectic_long_dyad_scale hEp]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLogTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-tail cubic estimate for the original logarithmically
varying weights, obtained by exact scalar normalization. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplecticAngularSmoothSum_const_mul (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (U t : ℝ) (z : ℂ) :
    metaplecticAngularSmoothSum r ℓ (fun x => z*W x) U t =
      z*metaplecticAngularSmoothSum r ℓ W U t := by
  unfold metaplecticAngularSmoothSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  ring

lemma logarithmic_tail_energy {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {s X : ℝ} (hs : 0 < s) (hX : 1 ≤ X)
    (w : Eisenstein → γ) (A : Finset Eisenstein) (hY : ∀ r ∈ A, Y (w r) ≤ X) (α : Eisenstein → ℂ) :
    (∑ r ∈ A, ‖α r*(((Y (w r))^s:ℝ):ℂ)‖^2) ≤ X^(2*s)*(∑ r ∈ A, ‖α r‖^2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hy : 0 < Y (w r) := zero_lt_one.trans_le (hW.length_one (w r))
  have hp : ((Y (w r))^s)^2 ≤ X^(2*s) := by
    calc
      _ ≤ (X^s)^2 := pow_le_pow_left₀ (Real.rpow_nonneg hy.le _)
        (Real.rpow_le_rpow hy.le (hY r hr) hs.le) 2
      _ = _ := by
        rw [←Real.rpow_mul_natCast (zero_lt_one.trans_le hX).le]
        congr 1
        push_cast
        ring
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hy.le _),mul_pow]
  exact (mul_le_mul_of_nonneg_left hp (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem LogarithmicWeightFamily.metaplectic_tail_dyad_sieve
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {ε s : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A S : Finset Eisenstein) (X N U B C F E : ℝ),
      1 ≤ X → 1 ≤ N → 0 < U → 0 ≤ B → 1 ≤ E →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ e ∈ S, primary e ∧ E ≤ norm e ∧ norm e ≤ 2*E) →
      (∀ r ∈ A, Y (w r) ≤ X) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ e ∈ S, ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0‖^2 ≤
        K*X^(2*s)*(N*(B*U))^ε*(B*U)*E^(2*ε)*
          (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := (hW.normalize hs).metaplectic_tail_dyad_sieve hε hεsmall
  refine ⟨K,hK,?_⟩
  intro w A S X N U B C F E hX hN hU hB hE hA hS hY hcut α ℓ
  let α' : Eisenstein → ℂ := fun r => α r*(((Y (w r))^s:ℝ):ℂ)
  have hncut (r : Eisenstein) (hr : r ∈ A) (x : ℝ) (hx : B < x) :
      normalizedLogWeight Y W s (w r) x = 0 := by
    simp only [normalizedLogWeight,hcut r hr x hx,smul_zero]
  have hb := hbound w A S N U B C F E hN hU hB hE hA hS hncut α' ℓ
  have heq : (∑ e ∈ S, ∑ r ∈ A, α' r*metaplecticTailCoefficient r ℓ C F e*
      metaplecticAngularSmoothSum r ℓ (normalizedLogWeight Y W s (w r)) (U/norm e^3) 0) =
      ∑ e ∈ S, ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0 := by
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro r _
    have hy : 0 < Y (w r) := zero_lt_one.trans_le (hW.length_one (w r))
    have hlin : metaplecticAngularSmoothSum r ℓ (normalizedLogWeight Y W s (w r)) (U/norm e^3) 0 =
        (((Y (w r))^(-s):ℝ):ℂ)*metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0 := by
      change metaplecticAngularSmoothSum r ℓ (fun x => ((Y (w r))^(-s):ℝ) • W (w r) x) _ _ = _
      simp_rw [Complex.real_smul]
      exact metaplecticAngularSmoothSum_const_mul r ℓ (W (w r)) _ _ _
    have hp : (((Y (w r))^s:ℝ):ℂ)*(((Y (w r))^(-s):ℝ):ℂ) = 1 := by
      rw [←Complex.ofReal_mul,←Real.rpow_add hy,add_neg_cancel,Real.rpow_zero,Complex.ofReal_one]
    rw [hlin]
    dsimp [α']
    calc
      _ = ((((Y (w r))^s:ℝ):ℂ)*(((Y (w r))^(-s):ℝ):ℂ))*
          (α r*metaplecticTailCoefficient r ℓ C F e*
            metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0) := by ring
      _ = _ := by rw [hp,one_mul]
  rw [heq] at hb
  apply hb.trans
  have henergy := logarithmic_tail_energy hW hs hX w A hY α
  calc
    _ ≤ K*(N*(B*U))^ε*(B*U)*E^(2*ε)*
        (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(X^(2*s)*(∑ r ∈ A, ‖α r‖^2)) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual long inverse-completion sum, collected by e=cd.
The resulting weight is the proved tail coefficient, not an arbitrary
divisor-bounded replacement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_long_completion_collect (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (C : ℝ) :
    metaplecticLongCompletion r ℓ W U C F =
      ∑ e ∈ ((primaryElementBall F).product (primaryElementBall F)).image
        (fun cd => cd.1*cd.2), metaplecticTailCoefficient r ℓ C F e*
          metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0 := by
  rw [←metaplecticTailCoefficient_collect]
  unfold metaplecticLongCompletion
  apply Finset.sum_congr rfl
  intro c hc
  have hcp := (mem_primaryElementBall.mp hc).1
  have hNc := norm_pos_of_ne_zero (primary_ne_zero hcp)
  have hV : 0 < U/norm c^3 := div_pos hU (pow_pos hNc 3)
  have hVU : U/norm c^3 ≤ U := div_le_self hU.le
    (one_le_pow₀ (one_le_norm (primary_ne_zero hcp)))
  have hBV : B*(U/norm c^3) ≤ F := (mul_le_mul_of_nonneg_left hVU hB).trans hBF
  by_cases hC : C < norm c
  · rw [ite_eq_left hC,metaplectic_forward_completion r ℓ W hV hB hBV hW,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [ite_eq_left hC]
    have he : U/norm c^3/norm d^3 = U/norm (c*d)^3 := by
      rw [norm_mul_eq,mul_pow]
      field_simp
    rw [he]
    ring
  · simp only [hC,ite_false, if_false,zero_mul,Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual long inverse sum has a finite, canonical norm-dyad
partition. Each nonempty block lies above half the inverse cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticLongSupport_primary {C F : ℝ} {e : Eisenstein}
    (he : e ∈ metaplecticLongSupport C F) : primary e := by
  obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
  exact primary_mul (mem_primaryElementBall.mp hc).1 (mem_primaryElementBall.mp hd).1

lemma metaplecticLongSupport_norm {C F : ℝ} (hF : 0 ≤ F) {e : Eisenstein}
    (he : e ∈ metaplecticLongSupport C F) : norm e ≤ F^2 := by
  obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
  rw [norm_mul_eq,pow_two]
  exact mul_le_mul (mem_primaryElementBall.mp hc).2 (mem_primaryElementBall.mp hd).2
    (norm_nonneg _) hF

lemma metaplecticLongDyad_norm {C F : ℝ} {j : ℕ} {e : Eisenstein}
    (he : e ∈ metaplecticLongDyad C F j) :
    primary e ∧ (2:ℝ)^j ≤ norm e ∧ norm e ≤ 2*(2:ℝ)^j := by
  obtain ⟨hs,hj⟩ := Finset.mem_filter.mp he
  have hp := metaplecticLongSupport_primary hs
  have hd : e ∈ frequencyDyad j := mem_frequencyDyad.mpr ⟨primary_ne_zero hp,hj⟩
  have hn := frequencyDyad_norm hd
  exact ⟨hp,hn.1,hn.2⟩

lemma metaplecticLongDyad_cutoff {C F : ℝ} {j : ℕ}
    (hj : j ∈ metaplecticLongDyads C F) : C < 2*(2:ℝ)^j := by
  obtain ⟨e,he,hlog⟩ := Finset.mem_image.mp hj
  have hmem : e ∈ metaplecticLongDyad C F j := Finset.mem_filter.mpr ⟨he,hlog⟩
  exact (Finset.mem_filter.mp he).2.trans_le (metaplecticLongDyad_norm hmem).2.2

theorem metaplectic_long_completion_active (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (C : ℝ) :
    metaplecticLongCompletion r ℓ W U C F =
      ∑ e ∈ metaplecticLongSupport C F, metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0 := by
  rw [metaplectic_long_completion_collect r ℓ W hU hB hBF hW C]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hn
  have hp : primary e := by
    obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    exact primary_mul (mem_primaryElementBall.mp hc).1 (mem_primaryElementBall.mp hd).1
  have hCe : norm e ≤ C := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨he,lt_of_not_ge h⟩)
  rw [metaplecticTailCoefficient_zero r ℓ hp hCe,zero_mul]

lemma metaplectic_long_dyad_partition (C F : ℝ) (f : Eisenstein → ℂ) :
    (∑ e ∈ metaplecticLongSupport C F, f e) =
      ∑ j ∈ metaplecticLongDyads C F, ∑ e ∈ metaplecticLongDyad C F j, f e := by
  exact (Finset.sum_fiberwise_of_maps_to
    (fun e he => Finset.mem_image_of_mem (fun e => Nat.log 2 (normNat e)) he) f).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical finite dyads sum to the actual long inverse completion.
The squared estimate keeps the square of the number of active dyads. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplecticLongDyad_scale {C F : ℝ} (hF : 0 ≤ F) {j : ℕ}
    (hj : j ∈ metaplecticLongDyads C F) : (2:ℝ)^j ≤ F^2 := by
  obtain ⟨e,he,hj'⟩ := Finset.mem_image.mp hj
  have hmem : e ∈ metaplecticLongDyad C F j := Finset.mem_filter.mpr ⟨he,hj'⟩
  exact (metaplecticLongDyad_norm hmem).2.1.trans (metaplecticLongSupport_norm hF he)

lemma metaplectic_long_outer_partition (A : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) (W : Eisenstein → ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hF : B*U ≤ F)
    (hcut : ∀ r ∈ A, ∀ x : ℝ, B < x → W r x = 0) (C : ℝ) :
    (∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W r) U C F) =
      ∑ j ∈ metaplecticLongDyads C F, ∑ e ∈ metaplecticLongDyad C F j,
        ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
          metaplecticAngularSmoothSum r ℓ (W r) (U/norm e^3) 0 := by
  calc
    _ = ∑ r ∈ A, ∑ j ∈ metaplecticLongDyads C F,
        ∑ e ∈ metaplecticLongDyad C F j, α r*metaplecticTailCoefficient r ℓ C F e*
          metaplecticAngularSmoothSum r ℓ (W r) (U/norm e^3) 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [metaplectic_long_completion_active r ℓ (W r) hU hB hF (hcut r hr) C,
        metaplectic_long_dyad_partition]
      simp only [Finset.mul_sum,mul_assoc]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]

lemma metaplectic_long_cutoff_ratio {C E U : ℝ}
    (hC : 0 < C) (hCE : C ≤ 2*E) (hU : 0 ≤ U) :
    U/E^3 ≤ 8*U/C^3 := by
  have hE : 0 < E := by linarith
  have hCE' : C/2 ≤ E := by linarith
  calc
    _ ≤ U/(C/2)^3 := div_le_div_of_nonneg_left hU (by positivity)
      (pow_le_pow_left₀ (by positivity) hCE' 3)
    _ = _ := by field_simp; ring

lemma metaplectic_long_dyad_power {F E ε : ℝ}
    (hF : 1 ≤ F) (hE : 0 ≤ E) (hEF : E ≤ F^2) (hε : 0 ≤ ε) :
    E^(2*ε) ≤ F^(4*ε) := by
  calc
    _ ≤ (F^2)^(2*ε) := Real.rpow_le_rpow hE hEF (by positivity)
    _ = _ := by
      rw [←Real.rpow_natCast F 2,←Real.rpow_mul (by linarith : 0 ≤ F)]
      congr 1
      ring

theorem LogarithmicWeightFamily.metaplectic_long_sieve_oai
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {ε s : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein)
      (X N U B C F : ℝ), 1 ≤ X → 1 ≤ N → 0 < U → 0 ≤ B →
      0 < C → 1 ≤ F → B*U ≤ F →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ r ∈ A, Y (w r) ≤ X) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W (w r)) U C F‖^2 ≤
        K*((metaplecticLongDyads C F).card:ℝ)^2*X^(2*s)*(N*(B*U))^ε*(B*U)*F^(4*ε)*
          (N+8*B*U/C^3+(8*N*B*U/C^3)^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_tail_dyad_sieve hε hεsmall hs
  refine ⟨K,hK,?_⟩
  intro w A X N U B C F hX hN hU hB hC hF hBU hA hY hcut α ℓ
  let J := metaplecticLongDyads C F
  let f : ℕ → ℂ := fun j => ∑ e ∈ metaplecticLongDyad C F j,
    ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
      metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0
  let M : ℝ := K*X^(2*s)*(N*(B*U))^ε*(B*U)*F^(4*ε)*
    (N+8*B*U/C^3+(8*N*B*U/C^3)^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2)
  have hb (j : ℕ) (hj : j ∈ J) : ‖f j‖^2 ≤ M := by
    have hE : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have he := metaplectic_long_dyad_power hF (by positivity)
      (metaplecticLongDyad_scale (by linarith) hj) hε.le
    have hz := metaplectic_long_cutoff_ratio hC
      (metaplecticLongDyad_cutoff hj).le hU.le
    have hshape : N+B*(U/((2:ℝ)^j)^3)+
        (N*(B*(U/((2:ℝ)^j)^3)))^(2/3:ℝ) ≤
        N+8*B*U/C^3+(8*N*B*U/C^3)^(2/3:ℝ) := by
      have hz' : B*(U/((2:ℝ)^j)^3) ≤ 8*B*U/C^3 := by
        convert mul_le_mul_of_nonneg_left hz hB using 1
        all_goals try with_reducible_and_instances rfl
        ring
      have hn' : N*(B*(U/((2:ℝ)^j)^3)) ≤ 8*N*B*U/C^3 := by
        convert mul_le_mul_of_nonneg_left hz' (by linarith : 0 ≤ N) using 1
        all_goals try with_reducible_and_instances rfl
        ring
      exact add_le_add (add_le_add le_rfl hz')
        (Real.rpow_le_rpow (by positivity) hn' (by norm_num))
    have hh := hbound w A (metaplecticLongDyad C F j) X N U B C F ((2:ℝ)^j)
      hX hN hU hB hE hA (fun e he => metaplecticLongDyad_norm he) hY hcut α ℓ
    apply hh.trans
    dsimp [M]
    gcongr
  rw [metaplectic_long_outer_partition A α ℓ (fun r => W (w r)) hU hB hBU hcut C]
  change ‖∑ j ∈ J, f j‖^2 ≤ _
  have hCS : ‖∑ j ∈ J, f j‖^2 ≤ (J.card:ℝ)*(∑ j ∈ J, ‖f j‖^2) := by
    simpa using complex_bilinear_rows_sq J (fun _ => (1:ℂ)) f
  calc
    _ ≤ (J.card:ℝ)*(∑ j ∈ J, ‖f j‖^2) := hCS
    _ ≤ (J.card:ℝ)*(∑ _j ∈ J, M) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum hb) (Nat.cast_nonneg _)
    _ = _ := by simp [M,J]; ring

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve_oai.{u_1} := @OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve_oai.{u_1}
