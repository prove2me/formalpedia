-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_scaleFirstStoppedLate_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:12:40.194409+00:00
-- url     : https://prove2.me/submissions/f7f6f7a6-3192-4d57-9801-a838d5f662d1

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A015
import Theorems.Thm_OAI_CubicFirstMoment_sieveExponent_four_thirds

section
-- module Solutions.OAIQ096_CM.Compat
attribute [-instance] _root_.instMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

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
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformWeightMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform support and derivative bounds survive the compact family
of logarithmic-denominator multipliers used in the original coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma UniformLogWeights.norm_bound {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i x, ‖W i x‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := h.derivative_bound 0
  refine ⟨M,hM,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he : Real.exp (-(-Real.log x)) = x := by simp [Real.exp_log hx]
    have hb := hbound i (-Real.log x)
    simpa only [norm_iteratedFDeriv_zero,he] using hb
  · have hz : W i x = 0 := by
      by_contra hn
      have hp := h.positive i (subset_closure hn)
      exact hx hp
    simpa only [hz,norm_zero] using hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLatticeModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primaryFactorRemainder_spec {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    primary (primaryFactorRemainder n s) ∧ Squarefree (primaryFactorRemainder n s) ∧
      (∏ p ∈ s, p)*primaryFactorRemainder n s = n := by
  have hp : ∀ p ∈ primaryPrimeFactors n \ s, primaryPrime p :=
    fun p h => (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp h).1).1
  refine ⟨primary_finset_prod _ _ (fun p h => (hp p h).1),
    primaryPrime_product_squarefree _ hp,?_⟩
  rw [primaryFactorRemainder,mul_comm,Finset.prod_sdiff hsub,primaryPrimeFactors_prod hn hs]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primaryPairCoefficient_norm_le (S T : Finset Eisenstein)
    (hS : ∀ r ∈ S, primary r) (b : Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ p ∈ primaryPairFiber S T b, ‖w p‖ ≤ M) :
    ‖primaryPairCoefficient S T w b‖ ≤ ((S.filter (fun r => r ∣ b)).card:ℝ)*M := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hw).trans
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (primaryPairFiber_card_le S T hS b)) hM

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficientBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem stoppedAlpha_divisor_bound (E U : Finset Eisenstein)
    (hE : ∀ e ∈ E, primary e) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ)
    (remaining : Eisenstein → Prop) (a : Eisenstein) :
    ‖stoppedAlpha E U ψ w remaining a‖ ≤ ((E.filter (fun e => e ∣ a)).card:ℝ) := by
  apply (primaryPairCoefficient_norm_le E U hE a _ zero_le_one _).trans_eq (mul_one _)
  intro p hp
  by_cases he : remaining p.1
  · simpa only [ite_eq_left he] using cutoffMoebius_norm_le_one hψ w p.1
  · simp only [ite_eq_right he,norm_zero,zero_le_one]

theorem stoppedBeta_divisor_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (b : Eisenstein) :
    ‖stoppedBeta R D v ψ w selected b‖ ≤ ((R.filter (fun r => r ∣ b)).card:ℝ)*M := by
  apply primaryPairCoefficient_norm_le R D hR b _ hM
  intro p hp
  by_cases hs : selected p.1 p.2
  · simp only [ite_eq_left hs,norm_mul]
    exact (mul_le_mul_of_nonneg_left (cutoffMoebius_norm_le_one hψ w p.2)
      (_root_.norm_nonneg _)).trans ((mul_one _).le.trans
        (hv p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1))
  · simpa only [ite_eq_right hs,norm_zero] using hM

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

lemma geometricPrimeBin_index {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {p : Eisenstein} (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricPrimeBin ρ B p < geometricBinCount ρ B := by
  have hr := Real.log_pos hρ
  have hpn : 0 < norm p := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (primaryPrime_norm_ge_two hp)
  have hpρ : ρ ≤ norm p := hρ₂.trans (primaryPrime_norm_ge_two hp)
  have hl : 1 ≤ Real.log (norm p)/Real.log ρ := by
    apply (le_div_iff₀ hr).mpr
    rw [one_mul]
    exact Real.log_le_log (zero_lt_one.trans hρ) hpρ
  have hk : 1 ≤ ⌊Real.log (norm p)/Real.log ρ⌋₊ := (Nat.one_le_floor_iff _).mpr hl
  have hkM : ⌊Real.log (norm p)/Real.log ρ⌋₊ ≤ geometricBinCount ρ B := by
    exact (Nat.floor_mono (div_le_div_of_nonneg_right
      (Real.log_le_log hpn hpB) hr.le)).trans
        (Nat.floor_le_ceil _)
  unfold geometricPrimeBin
  omega

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished-tuple weight occurring in stopped coefficients.
Its multiplicity is bounded in terms of the fixed tuple length, so the
literal beta coefficient has one divisor-count loss independently of bins. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma distinguishedPrimeWeight_norm_le_one {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w z : ℝ) (p : Eisenstein) :
    ‖distinguishedPrimeWeight ψ w z p‖ ≤ 1 := by
  rw [distinguishedPrimeWeight,Complex.norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [(hψ (norm p/w)).1,(hψ (norm p/w)).2,
    (hψ (norm p/z)).1,(hψ (norm p/z)).2]

theorem distinguishedTupleCoefficient_norm (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (W : ι → Eisenstein → ℂ)
    (hW : ∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w z : ℝ) (r : Eisenstein) :
    ‖distinguishedTupleCoefficient S W ψ w z r‖ ≤
      ‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
        ((Fintype.card ι)^(Fintype.card ι):ℕ) := by
  unfold distinguishedTupleCoefficient
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  have hp (i : ι) (p : Eisenstein) (hp : p ∈ S i) :
      ‖W i p*distinguishedPrimeWeight ψ w z p‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hW i p hp) (distinguishedPrimeWeight_norm_le_one hψ w z p)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  simpa only [Finset.prod_const_one,mul_one] using
    orderedConvolution_norm_bound S (fun i p => W i p*distinguishedPrimeWeight ψ w z p)
      (fun _ => 1) hS (fun _ => zero_le_one) hp r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BoundedPrimeTuples
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded tuple lengths in the manuscript's actual
prime detector. The bound depends on xi, not on the envelope scale. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventually_prime_tuple_norm_bound {ξ C : ℝ} (hC : 0 < C)
    {k : ℕ} (hk : 1 < ξ*(k:ℝ)) :
    ∀ᶠ X : ℝ in atTop, C*X < (X^ξ)^k := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_const_mul_rpow_le hk (2*C)] with X hX h
  rw [Real.rpow_one] at h
  rw [←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans hX).le]
  nlinarith [mul_pos hC (zero_lt_one.trans hX)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughDivisorBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem stoppedBeta_rough_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    (selected : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M)
    {b : Eisenstein} (hb : primary b) (hs : Squarefree b) {k : ℕ} (hsize : norm b < w^k) :
    ‖stoppedBeta R D v ψ w selected b‖ ≤ (2^k:ℕ)*M := by
  apply (stoppedBeta_divisor_bound R D hR hψ w selected v hM hv b).trans
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
    (rough_primary_divisor_card R hR hb hs hw hrough hsize)) hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedRoughness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The roughness of the actual distinguished coefficient, followed by
a uniform bound for the stopped beta. Zero distinguished coefficients
are removed before counting divisors, so no support hypothesis is added. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem distinguishedTupleCoefficient_prime_support
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 0 < w) (hwz : w ≤ z) {r p : Eisenstein}
    (hr : distinguishedTupleCoefficient S W ψ w z r ≠ 0)
    (hp : primaryPrime p) (hpr : p ∣ r) : w < norm p ∧ norm p < 2*z := by
  have ho : orderedConvolution S (fun i q => W i q*distinguishedPrimeWeight ψ w z q) r ≠ 0 :=
    (mul_ne_zero_iff.mp hr).2
  obtain ⟨f,hf,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hfs,hfr⟩ := Finset.mem_filter.mp hf
  have hd : p ∣ ∏ i, f i := by rw [hfr]; exact hpr
  obtain ⟨i,_,hpi⟩ := (hp.2.dvd_finsetProd_iff f).mp hd
  have hfi := hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)
  have he : p = f i := primary_associated_eq hp.1 hfi.1
    ((hp.2.dvd_prime_iff_associated hfi.2).mp hpi)
  have hweight := (mul_ne_zero_iff.mp
    ((Finset.prod_ne_zero_iff.mp hterm) i (Finset.mem_univ i))).2
  rw [he]
  exact distinguishedPrimeWeight_support hψone hψzero hw hwz
    (zero_lt_one.trans_le (one_le_norm hfi.2.ne_zero)) hweight

lemma stoppedBeta_filter_nonzero (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop) (b : Eisenstein) :
    stoppedBeta (R.filter (fun r => v r ≠ 0)) D v ψ w selected b =
      stoppedBeta R D v ψ w selected b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_subset
  · intro q hq
    obtain ⟨hq,hprod⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqr,hqd⟩ := Finset.mem_product.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hqr).1,hqd⟩,hprod⟩
  · intro q hq hn
    obtain ⟨hq,hprod⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqr,hqd⟩ := Finset.mem_product.mp hq
    have hz : v q.1 = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hqr,h⟩,hqd⟩,hprod⟩)
    simp [hz]

/-- Literal beta has a fixed bound, independent of the number of bin
primes. Only distinguished prime factors are counted in its divisor fibre. -/
theorem stoppedBeta_distinguished_rough_bound
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (hW : ∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1)
    (R D : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 1 ≤ w) (hwz : w ≤ z)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hs : Squarefree b) {k : ℕ}
    (hsize : norm b < w^k) :
    ‖stoppedBeta R D (distinguishedTupleCoefficient S W ψ w z) ψ w selected b‖ ≤
      (2^k:ℕ)*(‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
        ((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  rw [←stoppedBeta_filter_nonzero]
  apply stoppedBeta_rough_bound _ D
    (fun r hr => hR r (Finset.mem_filter.mp hr).1) hψ w hw
  · intro r hr p hp
    have hpr := primaryPrimeFactor_spec (hR r (Finset.mem_filter.mp hr).1) hp
    exact (distinguishedTupleCoefficient_prime_support S hS W hψone hψzero
      (zero_lt_one.trans_le hw) hwz (Finset.mem_filter.mp hr).2 hpr.1 hpr.2).1.le
  · positivity
  · intro r _
    exact distinguishedTupleCoefficient_norm S hS W hW hψ w z r
  · exact hb
  · exact hs
  · exact hsize

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseBilinearPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sparse beta energy beats both the logarithmic alpha energy and
any fixed product-support dilation in the cubic bilinear sieve. -/
noncomputable section
namespace CubicFirstMoment

lemma sparse_bilinear_shape {X A B M : ℝ} (hX : 1 ≤ X)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 1 ≤ M)
    (hAX : A ≤ M*X^(2/3:ℝ)) (hBX : B ≤ M*X^(2/3:ℝ))
    (hAB : A*B ≤ M*X) :
    A+B+(A*B)^(2/3:ℝ) ≤ 3*M*X^(2/3:ℝ) := by
  have hp : M^(2/3:ℝ) ≤ M := by
    calc
      _ ≤ M^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
      _ = M := Real.rpow_one _
  have hb : (A*B)^(2/3:ℝ) ≤ M*X^(2/3:ℝ) := by
    calc
      _ ≤ (M*X)^(2/3:ℝ) := Real.rpow_le_rpow (mul_nonneg hA hB) hAB (by norm_num)
      _ = M^(2/3:ℝ)*X^(2/3:ℝ) := Real.mul_rpow (by linarith) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (by linarith) _)
  linarith

lemma sparse_bilinear_power_bound {X A B M δ H Kα Kβ : ℝ}
    (hX : 1 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 1 ≤ M)
    (hδ : 0 < δ) (_hH : 0 ≤ H) (hKα : 0 ≤ Kα) (hKβ : 0 ≤ Kβ)
    (d : ℕ) (hAX : A ≤ M*X^(2/3:ℝ)) (hBX : B ≤ M*X^(2/3:ℝ))
    (hAB : A*B ≤ M*X)
    (hlog : X^(-(δ/4))*(1+Real.log X)^d ≤ H) :
    (A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
        (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ)) ≤
      (3*Kα*Kβ*H*M^(2+δ/4))*X^(5/3-δ/2) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hpref : (A*B)^(δ/4) ≤ M^(δ/4)*X^(δ/4) := by
    simpa only [Real.mul_rpow hMp.le hXp.le] using
      Real.rpow_le_rpow (mul_nonneg hA hB) hAB (by positivity : 0 ≤ δ/4)
  have hshape := sparse_bilinear_shape hX hA hB hM hAX hBX hAB
  have hlog' : (1+Real.log X)^d ≤ H*X^(δ/4) := by
    have hh := mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hXp.le (δ/4))
    have he : X^(-(δ/4))*X^(δ/4) = 1 := by
      rw [←Real.rpow_add hXp]
      simp
    calc
      (1+Real.log X)^d = (X^(-(δ/4))*X^(δ/4))*(1+Real.log X)^d := by rw [he,one_mul]
      _ = X^(-(δ/4))*(1+Real.log X)^d*X^(δ/4) := by ring
      _ ≤ _ := hh
  have hL : 0 ≤ (1+Real.log X)^d := pow_nonneg (by linarith [Real.log_nonneg hX]) _
  have hbig :
      (A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*(A*B)*(1+Real.log X)^d*X^(-δ) ≤
      (M^(δ/4)*X^(δ/4))*(3*M*X^(2/3:ℝ))*(M*X)*(H*X^(δ/4))*X^(-δ) := by
    gcongr
  have hpow : X^(δ/4)*X^(2/3:ℝ)*X*X^(δ/4)*X^(-δ) = X^(5/3-δ/2) := by
    nth_rw 3 [←Real.rpow_one X]
    rw [←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp]
    congr 1
    ring
  have hm : M^(δ/4)*M*M = M^(2+δ/4) := by
    nth_rw 2 [←Real.rpow_one M]
    nth_rw 3 [←Real.rpow_one M]
    rw [←Real.rpow_add hMp,←Real.rpow_add hMp]
    congr 1
    ring
  calc
    _ = (Kα*Kβ)*((A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*(A*B)*
        (1+Real.log X)^d*X^(-δ)) := by ring
    _ ≤ (Kα*Kβ)*((M^(δ/4)*X^(δ/4))*(3*M*X^(2/3:ℝ))*(M*X)*
        (H*X^(δ/4))*X^(-δ)) := mul_le_mul_of_nonneg_left hbig (mul_nonneg hKα hKβ)
    _ = (3*Kα*Kβ*H)*(M^(δ/4)*M*M)*
        (X^(δ/4)*X^(2/3:ℝ)*X*X^(δ/4)*X^(-δ)) := by ring
    _ = _ := by rw [hm,hpow]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PowerSavings
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Power savings at the first-moment scale

A fixed power saving is smaller than `X^(5/6) / log X`.  This is the
analytic bookkeeping used for the short-range and truncation errors in
the sharp-cutoff argument.
-/

noncomputable section

open Filter Asymptotics

namespace CubicFirstMoment

/-- Any fixed positive power saving is negligible at the asserted scale. -/
theorem powerSaving_isLittleO {δ : ℝ} (hδ : 0 < δ) :
    (fun X : ℝ => X ^ (5 / 6 - δ : ℝ)) =o[atTop] firstMomentScale := by
  let multiplier : ℝ → ℝ := fun X => X ^ (5 / 6 - δ : ℝ) / Real.log X
  have h := (isLittleO_log_rpow_atTop hδ).mul_isBigO
    (isBigO_refl multiplier atTop)
  apply h.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    dsimp [multiplier]
    field_simp [(Real.log_pos hX).ne']
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    dsimp [multiplier, firstMomentScale]
    rw [← mul_div_assoc, ← Real.rpow_add (by linarith : 0 < X)]
    congr 2
    ring

/-- A bound with a fixed power saving implies the required little-oh
bound for any normed target space. -/
theorem isLittleO_of_powerSaving {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {δ : ℝ} (hδ : 0 < δ)
    (hf : f =O[atTop] (fun X : ℝ => X ^ (5 / 6 - δ : ℝ))) :
    f =o[atTop] firstMomentScale :=
  hf.trans_isLittleO (powerSaving_isLittleO hδ)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The elementary prime model from the ordinary prime ideal theorem

The only number-theoretic hypothesis used here is the ordinary asymptotic
for the number of primary prime elements.  The power-weighted consequence
is derived by Abel summation.
-/

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

private lemma primaryPrimeFiber_eq (n : ℕ) (X : ℝ) (hn : (n : ℝ) ≤ X) :
    (primeCutoff (n : ℝ)).filter (fun p => normNat p = n) =
      (primeCutoff X).filter (fun p => normNat p = n) := by
  ext p
  simp only [Finset.mem_filter, mem_primeCutoff]
  constructor
  · intro hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hn⟩, hp.2⟩
  · intro hp
    have he : norm p = (n : ℝ) := by rw [← normNat_cast p, hp.2]
    exact ⟨⟨hp.1.1, he.le⟩, hp.2⟩

lemma primaryPrimeMultiplicity_zero : primaryPrimeMultiplicity 0 = 0 := by
  have he : (primeCutoff (0 : ℝ)).filter (fun p => normNat p = 0) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hp' := (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
    have hn : norm p = 0 := by
      rw [← normNat_cast p, (Finset.mem_filter.mp hp).2, Nat.cast_zero]
    have hz : p = 0 := by
      apply Subtype.ext
      exact Complex.normSq_eq_zero.mp hn
    exact hp'.2.ne_zero hz
  simp only [primaryPrimeMultiplicity, Nat.cast_zero, he, Finset.card_empty]

lemma primeNorm_sum_eq (g : ℕ → ℝ) {X : ℝ} (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, g n * primaryPrimeMultiplicity n) =
      ∑ p ∈ primeCutoff X, g (normNat p) := by
  have hmaps : ∀ p ∈ primeCutoff X, normNat p ∈ Finset.Icc 0 ⌊X⌋₊ := by
    intro p hp
    simp only [Finset.mem_Icc, Nat.zero_le, true_and]
    apply (Nat.le_floor_iff hX).mpr
    rw [normNat_cast]
    exact (mem_primeCutoff.mp hp).2
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps g]
  apply Finset.sum_congr rfl
  intro n hn
  have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX).mp (Finset.mem_Icc.mp hn).2
  rw [primaryPrimeMultiplicity, primaryPrimeFiber_eq n X hnX]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

lemma normCountingSum_primaryPrimeMultiplicity {X : ℝ} (hX : 0 ≤ X) :
    normCountingSum primaryPrimeMultiplicity X = primaryPrimeCount X := by
  simpa only [normCountingSum, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one,
    primaryPrimeCount] using primeNorm_sum_eq (fun _ => 1) hX

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticWeightedBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelOverlapCounting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseEnvelopeWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed product envelope in the sparse branch gives an actual
uniform family of inner weights on every fixed outer norm dyad. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma log_dyad_ratio {a A M : ℝ} (hA : 0 < A) (_hM : 1 ≤ M)
    (ha : A ≤ a) (haM : a ≤ M*A) :
    0 < a/A ∧ |Real.log (a/A)| ≤ Real.log M := by
  have hratio : 1 ≤ a/A := (le_div_iff₀ hA).mpr (by simpa using ha)
  have hupper : a/A ≤ M := (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using haM)
  refine ⟨zero_lt_one.trans_le hratio,?_⟩
  rw [abs_of_nonneg (Real.log_nonneg hratio)]
  exact Real.log_le_log (zero_lt_one.trans_le hratio) hupper

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogPowerSaving
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial logarithmic cost of the central integral is absorbed
by the already proved fixed power saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem log_power_powerSaving_isLittleO (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (fun X : ℝ => (1+Real.log X)^d*X^(5/6-δ)) =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := log_power_normalization_bound d (show 0 < δ/2 by positivity)
  apply isLittleO_of_powerSaving (show 0 < δ/2 by positivity)
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  have he : X^(-(δ/2))*X^(5/6-δ/2) = X^(5/6-δ) := by
    rw [←Real.rpow_add hXp]
    congr 1
    ring
  calc
    _ = (X^(-(δ/2))*(1+Real.log X)^d)*X^(5/6-δ/2) := by rw [←he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbound X hX) (Real.rpow_nonneg hXp.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedUniform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for the literal stopped distinguished coefficient on
the fixed X-envelope. The bin boundary parameter does not enter them. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_uniform {ξ C : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hC : 0 < C)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D : Finset Eisenstein) (selected : Eisenstein → Eisenstein → Prop),
      (∀ i, ∀ p ∈ S i, primaryPrime p) →
      (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) → (∀ r ∈ R, primary r) →
      ∀ b : Eisenstein, primary b → Squarefree b → norm b ≤ C*X →
        ‖stoppedBeta R D (distinguishedTupleCoefficient S W ψ (X^ξ) (X^(2/5:ℝ)))
          ψ (X^ξ) selected b‖ ≤ K := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ξ)
  have hk' : 1 < ξ*(k:ℝ) := by
    have hh := (div_lt_iff₀ hξ).mp hk
    nlinarith
  let M : ℝ := ‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
    ((Fintype.card ι)^(Fintype.card ι):ℕ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨(2^k:ℕ)*(M+1),by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_prime_tuple_norm_bound hC hk']
    with X hX hnorm
  intro S W R D selected hS hW hR b hb hs hbX
  apply (stoppedBeta_distinguished_rough_bound S hS W hW R D hR hψ hψone hψzero
    (Real.one_le_rpow hX.le hξ.le) (Real.rpow_le_rpow_of_exponent_le hX.le hξz)
    selected hb hs (hbX.trans_lt hnorm)).trans
  change (2^k:ℕ)*M ≤ (2^k:ℕ)*(M+1)
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeUpper
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeReciprocal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime reciprocal estimate used in the smooth-number discard,
derived from ordinary prime counting by literal Abel summation. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma primaryPrimeMultiplicity_one : primaryPrimeMultiplicity 1 = 0 := by
  have he : (primeCutoff (1:ℝ)).filter (fun p => normNat p = 1) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hpp := (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
    have hn : norm p = 1 := by
      rw [←normNat_cast p,(Finset.mem_filter.mp hp).2,Nat.cast_one]
    exact hpp.2.not_isUnit (isUnit_of_norm_eq_one hn)
  simp only [primaryPrimeMultiplicity,Nat.cast_one,he,Finset.card_empty,Nat.cast_zero]

private lemma inverse_square_continuous (X : ℝ) :
    ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc 2 X) := by
  apply (continuousOn_id.pow 2).inv₀
  intro t ht
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))

lemma primaryPrime_reciprocal_integrable {X : ℝ} (hX : 2 ≤ X) :
    IntervalIntegrable (fun t => primaryPrimeCount t/t^2) volume 2 X := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr
  have h := integrableOn_mul_sum_Icc (c := primaryPrimeMultiplicity)
    (m := 0) (a := 2) (b := X) (by norm_num)
    (inverse_square_continuous X).integrableOn_Icc
  apply h.congr_fun _ measurableSet_Icc
  intro t ht
  change (t^2)⁻¹*normCountingSum primaryPrimeMultiplicity t = _
  rw [normCountingSum_primaryPrimeMultiplicity (by linarith [ht.1])]
  ring

lemma primaryPrime_reciprocal_identity {X : ℝ} (hX : 2 ≤ X) :
    (∑ p ∈ primeCutoff X, (norm p)⁻¹) = primaryPrimeCount X/X+
      ∫ t in 2..X, primaryPrimeCount t/t^2 := by
  have hdiff : ∀ t ∈ Set.Icc (2:ℝ) X,
      DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc (2:ℝ) X,
      deriv (fun x : ℝ => x⁻¹) t = -(t^2)⁻¹ := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))).deriv
  have hint : IntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Set.Icc 2 X) := by
    exact ((inverse_square_continuous X).neg.integrableOn_Icc).congr_fun
      (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ (c := primaryPrimeMultiplicity)
    primaryPrimeMultiplicity_zero primaryPrimeMultiplicity_one X hdiff hint
  rw [primeNorm_sum_eq (fun n => (n:ℝ)⁻¹) (by linarith)] at h
  change (∑ p ∈ primeCutoff X, (normNat p:ℝ)⁻¹) =
    X⁻¹*normCountingSum primaryPrimeMultiplicity X-
      ∫ t in Set.Ioc 2 X, deriv (fun x : ℝ => x⁻¹) t*
        normCountingSum primaryPrimeMultiplicity t at h
  rw [normCountingSum_primaryPrimeMultiplicity (by linarith),
    ←intervalIntegral.integral_of_le hX] at h
  have hi : (∫ t in 2..X, deriv (fun x : ℝ => x⁻¹) t*
      normCountingSum primaryPrimeMultiplicity t) =
      -(∫ t in 2..X, primaryPrimeCount t/t^2) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    dsimp only
    rw [hderiv t ht,normCountingSum_primaryPrimeMultiplicity (by linarith [ht.1])]
    ring
  rw [hi] at h
  simpa only [normNat_cast,sub_neg_eq_add,div_eq_mul_inv,mul_comm] using h

theorem primaryPrime_reciprocal_upper (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
      (∑ p ∈ primeCutoff X, (norm p)⁻¹) ≤
        C/Real.log X+C*(Real.log (Real.log X)-Real.log (Real.log 2)) := by
  obtain ⟨C,hC,hcount⟩ := primaryPrimeCount_upper hpnt
  refine ⟨C,hC,?_⟩
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hlog : 0 < Real.log X := Real.log_pos (lt_of_lt_of_le (by norm_num) hX)
  rw [primaryPrime_reciprocal_identity hX]
  apply add_le_add
  · calc
      _ ≤ (C*X/Real.log X)/X := div_le_div_of_nonneg_right (hcount X hX) hX0.le
      _ = C/Real.log X := by field_simp
  · have hright : IntervalIntegrable (fun t : ℝ => t⁻¹/Real.log t) volume 2 X := by
      have hpos : ∀ t ∈ Set.uIcc (2:ℝ) X, 0 < t := by
        intro t ht
        rw [Set.uIcc_of_le hX] at ht
        exact lt_of_lt_of_le (by norm_num) ht.1
      have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc 2 X) :=
        continuousOn_id.inv₀ (fun t ht => (hpos t ht).ne')
      have hlog : ContinuousOn Real.log (Set.uIcc 2 X) :=
        Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')
      apply (hinv.div hlog _).intervalIntegrable
      intro t ht
      rw [Set.uIcc_of_le hX] at ht
      exact (Real.log_pos (lt_of_lt_of_le (by norm_num) ht.1)).ne'
    calc
      _ ≤ ∫ t in 2..X, C*(t⁻¹/Real.log t) := by
        apply intervalIntegral.integral_mono_on hX (primaryPrime_reciprocal_integrable hX)
          (hright.const_mul C)
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
        calc
          _ ≤ (C*t/Real.log t)/t^2 :=
            div_le_div_of_nonneg_right (hcount t ht.1) (sq_nonneg t)
          _ = C*(t⁻¹/Real.log t) := by field_simp
      _ = C*(Real.log (Real.log X)-Real.log (Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul,integral_inv_div_log (by norm_num)
          (lt_of_lt_of_le (by norm_num) hX)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeRankin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Rankin bounds for the actual primary squarefree elements.
The map to their prime-factor subsets is injective; no ideal-counting
or smooth-number estimate is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_supported_rankin_sum (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U) (σ : ℝ) :
    (∑ b ∈ S, norm b^(-σ)) ≤ ∏ p ∈ U, (1+norm p^(-σ)) := by
  rw [Finset.prod_one_add]
  apply OAI.sum_le_sum_of_injOn primaryPrimeFactors
  · intro b hb c hc he
    calc
      b = ∏ p ∈ primaryPrimeFactors b, p := (primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2).symm
      _ = ∏ p ∈ primaryPrimeFactors c, p := by rw [he]
      _ = c := primaryPrimeFactors_prod (hS c hc).1 (hS c hc).2
  · intro s hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powerset.mpr (hU b hb)
  · intro b hb
    have hn : norm b = ∏ p ∈ primaryPrimeFactors b, norm p := by
      rw [←norm_finset_prod,primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2]
    rw [hn,Real.finsetProd_rpow _ _ (fun p _ => norm_nonneg p)]
  · intro s hs hnot
    exact Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (norm_nonneg p) _)

lemma finite_euler_product_le_exp (U : Finset Eisenstein) (σ : ℝ) :
    (∏ p ∈ U, (1+norm p^(-σ))) ≤ Real.exp (∑ p ∈ U, norm p^(-σ)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    exact add_nonneg zero_le_one (Real.rpow_nonneg (norm_nonneg p) _)
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp (norm p^(-σ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothRankinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth-number discard on the exp(sqrt(log X)) scale.
Only the ordinary prime number theorem is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_reciprocal_exp_bound (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∑ p ∈ primeCutoff (Real.exp T), (norm p)⁻¹) ≤ C*(1+Real.log T) := by
  obtain ⟨C,hC,hbound⟩ := primaryPrime_reciprocal_upper hpnt
  let K : ℝ := 1+|Real.log (Real.log 2)|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg (Real.log (Real.log 2))]
  refine ⟨C*K,mul_pos hC (zero_lt_one.trans_le hK),?_⟩
  intro T hT
  have h2 : (2:ℝ) ≤ Real.exp T := by
    have htwo : (2:ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1:ℝ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
    exact htwo.trans (Real.exp_le_exp.mpr hT)
  have hb := hbound (Real.exp T) h2
  simp only [Real.log_exp] at hb
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  calc
    _ ≤ C/T+C*(Real.log T-Real.log (Real.log 2)) := hb
    _ ≤ C+C*(Real.log T+|Real.log (Real.log 2)|) :=
      add_le_add (div_le_self hC.le hT)
        (mul_le_mul_of_nonneg_left (by linarith [neg_le_abs (Real.log (Real.log 2))]) hC.le)
    _ ≤ C*K*(1+Real.log T) := by
      dsimp [K]
      nlinarith [mul_nonneg (abs_nonneg (Real.log (Real.log 2))) hlog]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCharacterRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseLateGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The late-stop norm range in the manuscript supplies all length
hypotheses of the sparse cubic and model bounds, including fixed dyadic
dilations. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma late_stop_rectangle_bounds {X A B D : ℝ} (hX : 1 ≤ X) (hD : 1 ≤ D)
    (hB : X^(35/100:ℝ) ≤ B) (hBhi : B ≤ X^(40/100:ℝ))
    (hA : A ≤ D*X/B) :
    A ≤ D*X^(65/100:ℝ) ∧ B ≤ X ∧
      A ≤ D*X^(2/3:ℝ) ∧ B ≤ D*X^(2/3:ℝ) ∧ A*B ≤ D*X := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hp : 0 < X^(35/100:ℝ) := Real.rpow_pos_of_pos hXp _
  have hBp : 0 < B := hp.trans_le hB
  have hquot : X/X^(35/100:ℝ) = X^(65/100:ℝ) := by
    nth_rw 1 [←Real.rpow_one X]
    rw [←Real.rpow_sub hXp]
    norm_num
  have hAa : A ≤ D*X^(65/100:ℝ) := by
    calc
      _ ≤ D*(X/B) := by simpa only [mul_div_assoc] using hA
      _ ≤ D*(X/X^(35/100:ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hXp.le hp hB) (by linarith)
      _ = _ := by rw [hquot]
  refine ⟨hAa,?_,?_,?_,(le_div_iff₀ hBp).mp hA⟩
  · exact hBhi.trans (by simpa using
      Real.rpow_le_rpow_of_exponent_le hX (show (40/100:ℝ) ≤ 1 by norm_num))
  · exact hAa.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by norm_num)) (by linarith))
  · apply hBhi.trans
    apply (Real.rpow_le_rpow_of_exponent_le hX (show (40/100:ℝ) ≤ 2/3 by norm_num)).trans
    exact le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) hD

lemma eventually_late_stop_rectangle_bounds {D : ℝ} (hD : 1 ≤ D) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X^(35/100:ℝ) ≤ B → B ≤ X^(40/100:ℝ) → A ≤ D*X/B →
      A ≤ X ∧ B ≤ X ∧ A ≤ D*X^(2/3:ℝ) ∧
        B ≤ D*X^(2/3:ℝ) ∧ A*B ≤ D*X := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (65/100:ℝ) < 1 by norm_num) D] with X hX hDX
  intro A B hB hBhi hA
  obtain ⟨ha,hb,has,hbs,hab⟩ := late_stop_rectangle_bounds hX hD hB hBhi hA
  exact ⟨ha.trans (by simpa only [Real.rpow_one] using hDX),hb,has,hbs,hab⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeDivisorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second divisor moment on primary squarefree elements, from a
finite Euler product and the already specified ordinary prime theorem. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_four_reciprocal_sum (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U) :
    (∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card / norm b) ≤
      ∏ p ∈ U, (1+4/norm p) := by
  rw [Finset.prod_one_add]
  apply OAI.sum_le_sum_of_injOn primaryPrimeFactors
  · intro b hb c hc he
    calc
      b = ∏ p ∈ primaryPrimeFactors b, p :=
        (primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2).symm
      _ = ∏ p ∈ primaryPrimeFactors c, p := by rw [he]
      _ = c := primaryPrimeFactors_prod (hS c hc).1 (hS c hc).2
  · intro s hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powerset.mpr (hU b hb)
  · intro b hb
    have hn : norm b = ∏ p ∈ primaryPrimeFactors b, norm p := by
      rw [←norm_finset_prod,primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2]
    rw [Finset.prod_div_distrib,Finset.prod_const,hn]
  · intro s hs hnot
    exact Finset.prod_nonneg (fun p _ => div_nonneg (by norm_num) (norm_nonneg p))

lemma squarefree_four_sum_le_euler (S : Finset Eisenstein) {X : ℝ}
    (hX : 0 ≤ X) (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) :
    (∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card) ≤
      X*Real.exp (4*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
  have hsub : ∀ b ∈ S, primaryPrimeFactors b ⊆ primeCutoff X := by
    intro b hb p hp
    have hprime := primaryPrimeFactor_spec (hS b hb).1 hp
    exact mem_primeCutoff.mpr ⟨hprime.1,
      (norm_le_of_dvd_nonzero (primary_ne_zero (hS b hb).1) hprime.2).trans (hS b hb).2.2⟩
  have hprod : (∏ p ∈ primeCutoff X, (1+4/norm p)) ≤
      Real.exp (4*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      exact add_nonneg zero_le_one (div_nonneg (by norm_num) (norm_nonneg p))
    · intro p hp
      simpa only [div_eq_mul_inv,add_comm] using Real.add_one_le_exp (4*(norm p)⁻¹)
  calc
    _ ≤ ∑ b ∈ S, X*((4:ℝ)^(primaryPrimeFactors b).card/norm b) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb0 := norm_pos_of_ne_zero (primary_ne_zero (hS b hb).1)
      calc
        _ = norm b*((4:ℝ)^(primaryPrimeFactors b).card/norm b) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hS b hb).2.2 (by positivity)
    _ = X*∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card/norm b := by rw [Finset.mul_sum]
    _ ≤ X*(∏ p ∈ primeCutoff X, (1+4/norm p)) :=
      mul_le_mul_of_nonneg_left (squarefree_four_reciprocal_sum S (primeCutoff X)
        (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) hsub) hX
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hX

theorem squarefree_divisor_second_moment (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (X : ℝ) (S : Finset Eisenstein),
      Real.exp 1 ≤ X →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) →
      (∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card) ≤ K*X*(1+Real.log X)^d := by
  obtain ⟨C,hC,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  obtain ⟨d,hd⟩ := exists_nat_ge (4*C)
  refine ⟨Real.exp (4*C),d,Real.exp_pos _,?_⟩
  intro X S hX hS
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hl : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hl0 : 0 < Real.log X := zero_lt_one.trans_le hl
  have hrec := hprime (Real.log X) hl
  rw [Real.exp_log hX0] at hrec
  have he : Real.exp (4*(C*(1+Real.log (Real.log X)))) =
      Real.exp (4*C)*(Real.log X)^(4*C) := by
    rw [Real.rpow_def_of_pos hl0,←Real.exp_add]
    congr 1
    ring
  have hpow : (Real.log X)^(4*C) ≤ (1+Real.log X)^d := by
    calc
      _ ≤ (Real.log X)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le hl hd
      _ = (Real.log X)^d := Real.rpow_natCast _ _
      _ ≤ _ := pow_le_pow_left₀ hl0.le (by linarith : Real.log X ≤ 1+Real.log X) d
  calc
    _ ≤ X*Real.exp (4*∑ p ∈ primeCutoff X, (norm p)⁻¹) :=
      squarefree_four_sum_le_euler S hX0.le hS
    _ ≤ X*Real.exp (4*(C*(1+Real.log (Real.log X)))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hrec (by norm_num))) hX0.le
    _ = X*(Real.exp (4*C)*(Real.log X)^(4*C)) := by rw [he]
    _ ≤ X*(Real.exp (4*C)*(1+Real.log X)^d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)) hX0.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBStoppedAlphaEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic energy of the literal stopped outer coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_squarefree_divisor_card (E : Finset Eisenstein)
    (hE : ∀ e ∈ E, primary e) {a : Eisenstein} (ha : primary a) (hs : Squarefree a) :
    (E.filter (fun e => e ∣ a)).card ≤ 2^(primaryPrimeFactors a).card := by
  let T := E.filter (fun e => e ∣ a)
  have hcard : T.card ≤ (primaryPrimeFactors a).powerset.card := by
    apply Finset.card_le_card_of_injOn primaryPrimeFactors
    · intro e he
      apply Finset.mem_powerset.mpr
      intro p hp
      have hp' := primaryPrimeFactor_spec (hE e (Finset.mem_filter.mp he).1) hp
      exact primaryPrime_mem_factors ha hp'.1 (hp'.2.trans (Finset.mem_filter.mp he).2)
    · intro e he f hf heq
      have hes : Squarefree e := fun x hx => hs x (hx.trans (Finset.mem_filter.mp he).2)
      have hfs : Squarefree f := fun x hx => hs x (hx.trans (Finset.mem_filter.mp hf).2)
      calc
        e = ∏ p ∈ primaryPrimeFactors e, p :=
          (primaryPrimeFactors_prod (hE e (Finset.mem_filter.mp he).1) hes).symm
        _ = ∏ p ∈ primaryPrimeFactors f, p := by rw [heq]
        _ = f := primaryPrimeFactors_prod (hE f (Finset.mem_filter.mp hf).1) hfs
  exact hcard.trans_eq (Finset.card_powerset _)

theorem smallB_stopped_alpha_energy (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (E U S : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w X : ℝ) (remaining : Eisenstein → Prop),
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → Real.exp 1 ≤ X →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ X) →
      (∑ a ∈ S, ‖stoppedAlpha E U ψ w remaining a‖^2) ≤ K*X*(1+Real.log X)^d := by
  obtain ⟨K,d,hK,hmoment⟩ := squarefree_divisor_second_moment hpnt
  refine ⟨K,d,hK,?_⟩
  intro E U S ψ w X remaining hE hψ hX hS
  apply le_trans _ (hmoment X S hX hS)
  apply Finset.sum_le_sum
  intro a ha
  have hb : ‖stoppedAlpha E U ψ w remaining a‖ ≤
      (2:ℝ)^(primaryPrimeFactors a).card := by
    apply (stoppedAlpha_divisor_bound E U hE hψ w remaining a).trans
    exact_mod_cast primary_squarefree_divisor_card E hE (hS a ha).1 (hS a ha).2.1
  calc
    _ ≤ ((2:ℝ)^(primaryPrimeFactors a).card)^2 :=
      pow_le_pow_left₀ (_root_.norm_nonneg _) hb 2
    _ = (4:ℝ)^(primaryPrimeFactors a).card := by
      rw [←pow_mul, Nat.mul_comm, pow_mul]
      norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LateStopDivisor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A late ordinary stop contains the required large smooth divisor.
The divisor is the actual product of selected prime factors at or below
the roughness boundary, not an auxiliary existence hypothesis. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopped_late_smooth_divisor
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ) (Z Q M : ℝ)
    {r d : Eisenstein} (_hr : primary r) (hd : primary d) (hsd : Squarefree d)
    (hQ : 0 < Q) (hstop : stoppedSideTest bin ell j k h Z Q false r d)
    (hell : ∀ p ∈ primaryPrimeFactors d, 0 < ell (bin p) ∧ ell (bin p) ≤ norm p)
    (hsmall : ∀ p ∈ primaryPrimeFactors d, h ≤ bin p → norm p ≤ M) :
    primary (lateStopDivisor bin h d) ∧ Squarefree (lateStopDivisor bin h d) ∧
      lateStopDivisor bin h d ∣ r*d ∧ Z/Q < norm (lateStopDivisor bin h d) ∧
      ∀ p ∈ primaryPrimeFactors (lateStopDivisor bin h d), norm p ≤ M := by
  let U := (primaryPrimeFactors d).filter (fun p => h ≤ bin p)
  have hU : ∀ p ∈ U, primaryPrime p := fun p hp =>
    (primaryPrimeFactor_spec hd (Finset.mem_filter.mp hp).1).1
  have hprimary : primary (∏ p ∈ U, p) :=
    primary_finset_prod U (fun p => p) (fun p hp => (hU p hp).1)
  have hdiv : (∏ p ∈ U, p) ∣ d := by
    rw [←primaryPrimeFactors_prod hd hsd]
    exact Finset.prod_dvd_prod_of_subset U (primaryPrimeFactors d) (fun p => p)
      (Finset.filter_subset _ _)
  have hsplit : primeSurrogate (primaryPrimeFactors d) bin ell =
      primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell *
        primeSurrogate U bin ell := by
    unfold primeSurrogate primeBinPrefix
    rw [←Finset.prod_filter_mul_prod_filter_not (primaryPrimeFactors d) (fun p => bin p < h)]
    congr 1
    apply Finset.prod_congr
    · ext p
      simp only [U,Finset.mem_filter,not_lt]
    · intro p hp
      rfl
  have hlo : 0 < primeSurrogate U bin ell :=
    Finset.prod_pos (fun p hp => (hell p (Finset.mem_filter.mp hp).1).1)
  have hnorm : primeSurrogate U bin ell ≤ norm (∏ p ∈ U, p) := by
    rw [norm_finset_prod]
    apply Finset.prod_le_prod
    · intro p hp
      exact (hell p (Finset.mem_filter.mp hp).1).1.le
    · intro p hp
      exact (hell p (Finset.mem_filter.mp hp).1).2
  have hfailed : norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell < Q := by
    rcases hstop.2 with hf | hf
    · cases hf
    · exact hf
  have hcross : Z ≤ norm r*primeSurrogate (primaryPrimeFactors d) bin ell := hstop.1.2.2.2
  have hlarge : Z/Q < primeSurrogate U bin ell := by
    apply (div_lt_iff₀ hQ).mpr
    rw [hsplit,←mul_assoc] at hcross
    exact hcross.trans_lt (by nlinarith [mul_lt_mul_of_pos_right hfailed hlo])
  refine ⟨hprimary,primaryPrime_product_squarefree U hU,
    hdiv.trans (dvd_mul_left d r),hlarge.trans_le hnorm,?_⟩
  intro p hp
  change p ∈ primaryPrimeFactors (∏ q ∈ U, q) at hp
  rw [primaryPrimeFactors_finset_prod U hU] at hp
  exact hsmall p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseDivisorRankin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal mass of large squarefree divisors composed only of
polylogarithmically small primes. This is the Rankin step for sparse late
stops in the prime decomposition, derived from ordinary prime counting. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_reciprocal_rankin_tail (S U : Finset Eisenstein)
    (hS : ∀ d ∈ S, primary d ∧ Squarefree d)
    (hU : ∀ d ∈ S, primaryPrimeFactors d ⊆ U)
    {Y σ : ℝ} (hY : 0 < Y) (hσ : 0 ≤ σ)
    (hlarge : ∀ d ∈ S, Y ≤ norm d) :
    (∑ d ∈ S, (norm d)⁻¹) ≤
      Y^(-σ)*∏ p ∈ U, (1+norm p^(-(1-σ))) := by
  calc
    _ ≤ ∑ d ∈ S, Y^(-σ)*norm d^(-(1-σ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 := norm_pos_of_ne_zero (primary_ne_zero (hS d hd).1)
      calc
        _ = norm d^(-σ)*norm d^(-(1-σ)) := by
          rw [←Real.rpow_add hd0,show -σ + -(1-σ)=(-1:ℝ) by ring,Real.rpow_neg_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hY (hlarge d hd) (neg_nonpos.mpr hσ))
          (Real.rpow_nonneg hd0.le _)
    _ = Y^(-σ)*(∑ d ∈ S, norm d^(-(1-σ))) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (squarefree_supported_rankin_sum S U hS hU (1-σ)) (Real.rpow_nonneg hY.le _)

lemma prime_shifted_reciprocal_sum {y σ : ℝ} (_hy : 0 < y) (hσ : 0 ≤ σ) :
    (∑ p ∈ primeCutoff y, norm p^(-(1-σ))) ≤
      y^σ*(∑ p ∈ primeCutoff y, (norm p)⁻¹) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp0 := norm_pos_of_ne_zero (mem_primeCutoff.mp hp).1.2.ne_zero
  calc
    _ = norm p^σ*(norm p)⁻¹ := by
      rw [←Real.rpow_neg_one,←Real.rpow_add hp0]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hp0.le (mem_primeCutoff.mp hp).2 hσ) (inv_nonneg.mpr hp0.le)

private lemma power_log_sublinear (a b q : ℝ) (hq : q < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ T^q*(a+b*Real.log T) ≤ ε*T := by
  have hp : 0 < 1-q := sub_pos.mpr hq
  have hconst : (fun _ : ℝ => a) =o[atTop] (fun T => T^(1-q)) := by
    apply isLittleO_const_left.mpr
    right
    apply (tendsto_rpow_atTop hp).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact (Real.norm_of_nonneg (Real.rpow_nonneg hT.le _)).symm
  have hsmall := (hconst.add ((isLittleO_log_rpow_atTop hp).const_mul_left b)).def hε
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with T ht hT
  refine ⟨hT,?_⟩
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hT0.le _)] at ht
  have ht' : a+b*Real.log T ≤ ε*T^(1-q) := (le_abs_self _).trans ht
  calc
    _ ≤ T^q*(ε*T^(1-q)) :=
      mul_le_mul_of_nonneg_left ht' (Real.rpow_nonneg hT0.le _)
    _ = ε*T := by
      rw [←mul_assoc,mul_comm (T^q) ε,mul_assoc,←Real.rpow_add hT0,
        show q+(1-q)=1 by ring,Real.rpow_one]

/-- The precise sparse-divisor consequence needed for late stops.
The exponent depends on the fixed prime cutoff power and divisor size. -/
theorem polylog_smooth_divisor_reciprocal_saving
    (hpnt : PrimaryPrimePNT) {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      ∀ S : Finset Eisenstein,
      (∀ d ∈ S, primary d ∧ Squarefree d) →
      (∀ d ∈ S, X^η ≤ norm d) →
      (∀ d ∈ S, ∀ p ∈ primaryPrimeFactors d, norm p ≤ (Real.log X)^C) →
      (∑ d ∈ S, (norm d)⁻¹) ≤ X^(-δ) := by
  obtain ⟨K,hK,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  let σ : ℝ := (2*C)⁻¹
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hCs : C*σ = 1/2 := by dsimp [σ]; field_simp [hC.ne']
  let δ : ℝ := η*σ/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hy : Tendsto (fun X : ℝ => (Real.log X)^C) atTop atTop :=
    (tendsto_rpow_atTop hC).comp Real.tendsto_log_atTop
  refine ⟨δ,hδ,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp hy).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually
      (power_log_sublinear K (K*C) (1/2) (by norm_num) hδ)] with X hX hlogy hsmall
  intro S hS hlarge hsmooth
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL0 : 0 < Real.log X := Real.log_pos hX
  let y : ℝ := (Real.log X)^C
  have hy0 : 0 < y := Real.rpow_pos_of_pos hL0 C
  change 1 ≤ Real.log y at hlogy
  have hU : ∀ d ∈ S, primaryPrimeFactors d ⊆ primeCutoff y := by
    intro d hd p hp
    exact mem_primeCutoff.mpr ⟨(primaryPrimeFactor_spec (hS d hd).1 hp).1,hsmooth d hd p hp⟩
  have hrec : (∑ p ∈ primeCutoff y, (norm p)⁻¹) ≤ K*(1+C*Real.log (Real.log X)) := by
    have hh := hprime (Real.log y) hlogy
    rw [Real.exp_log hy0] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    have ht := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hlogy)
    have hlog : Real.log y = C*Real.log (Real.log X) := Real.log_rpow hL0 C
    rw [←hlog]
    linarith
  have hprod : (∏ p ∈ primeCutoff y, (1+norm p^(-(1-σ)))) ≤ X^δ := by
    apply (finite_euler_product_le_exp (primeCutoff y) (1-σ)).trans
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    apply (prime_shifted_reciprocal_sum hy0 hσ.le).trans
    apply (mul_le_mul_of_nonneg_left hrec (Real.rpow_nonneg hy0.le _)).trans
    have hp : y^σ = (Real.log X)^(1/2:ℝ) := by
      dsimp [y]
      rw [←Real.rpow_mul hL0.le,hCs]
    rw [hp]
    first | (convert hsmall.2 using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hsmall.2.trans (le_of_eq (by ring)))
  calc
    _ ≤ (X^η)^(-σ)*(∏ p ∈ primeCutoff y, (1+norm p^(-(1-σ)))) :=
      squarefree_reciprocal_rankin_tail S (primeCutoff y) hS hU
        (Real.rpow_pos_of_pos hX0 η) hσ.le hlarge
    _ ≤ (X^η)^(-σ)*X^δ := mul_le_mul_of_nonneg_left hprod
      (Real.rpow_nonneg (Real.rpow_nonneg hX0.le _) _)
    _ = X^(-δ) := by
      rw [←Real.rpow_mul hX0.le,←Real.rpow_add hX0]
      apply congrArg (fun t : ℝ => X^t)
      dsimp [δ]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseLateSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal sparse-support count: primary numbers containing a large
squarefree divisor made from small primes occupy a power-saving fraction
of a norm ball. The multiple count is the proved Eisenstein lattice bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisible_union_card (S D : Finset Eisenstein) {B : ℝ}
    (hB : 0 ≤ B) (hS : ∀ b ∈ S, b ≠ 0 ∧ norm b ≤ B)
    (hD : ∀ d ∈ D, d ≠ 0) (hcover : ∀ b ∈ S, ∃ d ∈ D, d ∣ b) :
    (S.card:ℝ) ≤ 18*B*(∑ d ∈ D, (norm d)⁻¹) := by
  have hsub : S ⊆ D.biUnion (fun d => S.filter (fun b => d ∣ b)) := by
    intro b hb
    obtain ⟨d,hd,hdiv⟩ := hcover b hb
    exact Finset.mem_biUnion.mpr ⟨d,hd,Finset.mem_filter.mpr ⟨hb,hdiv⟩⟩
  calc
    _ ≤ ∑ d ∈ D, ((S.filter (fun b => d ∣ b)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ d ∈ D, 18*B/norm d := Finset.sum_le_sum
      (fun d hd => divisible_row_card_le S hB hS d (hD d hd))
    _ = _ := by simp only [Finset.mul_sum,div_eq_mul_inv]

theorem sparseLateSupport_card_saving (hpnt : PrimaryPrimePNT)
    {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      ∀ B : ℝ, 0 ≤ B → ((sparseLateSupport X C η B).card:ℝ) ≤ 18*B*X^(-δ) := by
  obtain ⟨δ,hδ,hbound⟩ := polylog_smooth_divisor_reciprocal_saving hpnt hC hη
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hbound] with X hX
  intro B hB
  let S := sparseLateSupport X C η B
  let D := (primaryElementBall B).filter (fun d => Squarefree d ∧ X^η ≤ norm d ∧
    ∀ p ∈ primaryPrimeFactors d, norm p ≤ (Real.log X)^C)
  have hS : ∀ b ∈ S, b ≠ 0 ∧ norm b ≤ B := by
    intro b hb
    have hh := mem_primaryElementBall.mp (Finset.mem_filter.mp hb).1
    exact ⟨primary_ne_zero hh.1,hh.2⟩
  have hD : ∀ d ∈ D, primary d ∧ Squarefree d := by
    intro d hd
    exact ⟨(mem_primaryElementBall.mp (Finset.mem_filter.mp hd).1).1,
      (Finset.mem_filter.mp hd).2.1⟩
  have hcover : ∀ b ∈ S, ∃ d ∈ D, d ∣ b := by
    intro b hb
    obtain ⟨_,d,hd,hsd,hdiv,hsize,hsmooth⟩ := Finset.mem_filter.mp hb
    refine ⟨d,Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hd,?_⟩,
      hsd,hsize,hsmooth⟩,hdiv⟩
    exact (norm_le_of_dvd (hS b hb).1 hdiv).trans (hS b hb).2
  apply (divisible_union_card S D hB hS (fun d hd => primary_ne_zero (hD d hd).1) hcover).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hX D hD (fun d hd => (Finset.mem_filter.mp hd).2.2.1)
    (fun d hd => (Finset.mem_filter.mp hd).2.2.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseStoppedSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sparse support belongs to the actual late stopped coefficient.
Nonvanishing selects a literal product fibre, and the failed first stage
constructs its large small-prime divisor. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stoppedBeta_late_mem_sparse
    (R D : Finset Eisenstein) (f : Eisenstein → ℂ) (w : ℝ)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ)
    {X C η Z Q B : ℝ} (hQ : 0 < Q) (hgap : X^η ≤ Z/Q)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    (hell : ∀ d ∈ D, ∀ p ∈ primaryPrimeFactors d,
      0 < ell (bin p) ∧ ell (bin p) ≤ norm p)
    (hsmall : ∀ d ∈ D, ∀ p ∈ primaryPrimeFactors d,
      h ≤ bin p → norm p ≤ (Real.log X)^C)
    {b : Eisenstein} (hb : primary b) (hsb : Squarefree b) (hbB : norm b ≤ B)
    (hβ : stoppedBeta R D f primeDetectorCutoff w
      (stoppedSideTest bin ell j k h Z Q false) b ≠ 0) :
    b ∈ sparseLateSupport X C η B := by
  unfold stoppedBeta primaryPairCoefficient at hβ
  obtain ⟨t,ht,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  obtain ⟨hpair,heq⟩ := Finset.mem_filter.mp ht
  obtain ⟨hr,hd⟩ := Finset.mem_product.mp hpair
  have htest : stoppedSideTest bin ell j k h Z Q false t.1 t.2 := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  have hsd : Squarefree t.2 := by
    intro c hc
    apply hsb c
    exact hc.trans (heq ▸ dvd_mul_left t.2 t.1)
  obtain ⟨hc,hsc,hdiv,hlarge,hsmooth⟩ := stopped_late_smooth_divisor bin ell j k h Z Q
    ((Real.log X)^C) (hR _ hr) (hD _ hd) hsd hQ htest (hell _ hd) (hsmall _ hd)
  apply Finset.mem_filter.mpr
  refine ⟨mem_primaryElementBall.mpr ⟨hb,hbB⟩,
    lateStopDivisor bin h t.2,hc,hsc,?_,hgap.trans hlarge.le,hsmooth⟩
  exact heq ▸ hdiv

theorem sparse_stopped_beta_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C η ξ : ℝ} (hC : 0 < C) (hη : 0 < η)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B Z Q : ℝ), 0 ≤ B → B ≤ X → 0 < Q → X^η ≤ Z/Q →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D U : Finset Eisenstein) (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D, primary d) →
      (∀ d ∈ D, ∀ p ∈ primaryPrimeFactors d,
        0 < ell (bin p) ∧ ell (bin p) ≤ norm p) →
      (∀ d ∈ D, ∀ p ∈ primaryPrimeFactors d,
        h ≤ bin p → norm p ≤ (Real.log X)^C) →
      (∀ b ∈ U, primary b ∧ Squarefree b ∧ norm b ≤ B) →
      (∑ b ∈ U, ‖stoppedBeta R D
        (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
        primeDetectorCutoff (X^ξ) (stoppedSideTest bin ell j k h Z Q false) b‖^2) ≤
          K*B*X^(-δ) := by
  obtain ⟨δ,hδ,hcount⟩ := sparseLateSupport_card_saving hpnt hC hη
  obtain ⟨M,hM,hbound⟩ := stoppedBeta_distinguished_uniform (ι := ι) (C := 1) hξ hξz
    (by norm_num) (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx)
  refine ⟨δ,18*M^2,hδ,by positivity,?_⟩
  filter_upwards [hcount,hbound] with X hcount hbound
  intro B Z Q hB hBX hQ hgap S W R D U bin ell j k h hS hW hR hD hell hsmall hU
  let β := stoppedBeta R D
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ) (stoppedSideTest bin ell j k h Z Q false)
  let T := U.filter (fun b => β b ≠ 0)
  have hsub : T ⊆ sparseLateSupport X C η B := by
    intro b hb
    obtain ⟨hb,hβ⟩ := Finset.mem_filter.mp hb
    exact stoppedBeta_late_mem_sparse R D _ _ bin ell j k h hQ hgap hR hD hell hsmall
      (hU b hb).1 (hU b hb).2.1 (hU b hb).2.2 hβ
  have hcard : (T.card:ℝ) ≤ 18*B*X^(-δ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount B hB)
  have heq : (∑ b ∈ U, ‖β b‖^2) = ∑ b ∈ T, ‖β b‖^2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hz : β b = 0 <;> simp only [hz,ne_eq,not_true_eq_false,not_false_eq_true,
      ite_true, if_true,ite_false, if_false,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)]
  change (∑ b ∈ U, ‖β b‖^2) ≤ _
  rw [heq]
  calc
    _ ≤ ∑ _b ∈ T, M^2 := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hb,_⟩ := Finset.mem_filter.mp hb
      apply pow_le_pow_left₀ (_root_.norm_nonneg _)
      exact hbound S W R D _ hS hW hR b (hU b hb).1 (hU b hb).2.1
        (by simpa only [one_mul] using (hU b hb).2.2.trans hBX)
    _ = (T.card:ℝ)*M^2 := by simp
    _ ≤ (18*B*X^(-δ))*M^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseGeometricStop
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sparse-support hypotheses follow from the actual descending
geometric bins and the ordinary X^.36 then X^.38 stopping thresholds. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometric_late_prime_bound {ρ B M : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {h : ℕ} (hboundary : ρ*geometricBinLower ρ B h ≤ M)
    {p : Eisenstein} (hp : primaryPrime p) (hpB : norm p ≤ B)
    (hbin : h ≤ geometricPrimeBin ρ B p) : norm p ≤ M := by
  have hlower : geometricBinLower ρ B (geometricPrimeBin ρ B p) ≤
      geometricBinLower ρ B h := by
    apply pow_le_pow_right₀ hρ.le
    omega
  exact (((geometricPrimeBin_cell hρ hρ₂ hp hpB).2.trans_le
    (mul_le_mul_of_nonneg_left hlower (zero_le_one.trans hρ.le))).trans_le hboundary).le

lemma ordinary_late_threshold_ratio {X : ℝ} (hX : 0 < X) :
    X^(38/100:ℝ)/X^(36/100:ℝ) = X^(1/50:ℝ) := by
  rw [←Real.rpow_sub hX]
  norm_num

/-- The literal ordinary late-stop coefficient has power-saving energy.
Only the concrete location of the roughness boundary is required; the
large divisor and its sparse multiple support follow from the stopping condition. -/
theorem ordinary_late_stopped_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ : ℝ), 0 ≤ B → B ≤ X → 1 < ρ → ρ ≤ 2 →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D U : Finset Eisenstein),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D, primary d ∧ norm d ≤ X) →
      (∀ b ∈ U, primary b ∧ Squarefree b ∧ norm b ≤ B) →
      (∑ b ∈ U, ‖stoppedBeta R D
        (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
        primeDetectorCutoff (X^ξ)
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b‖^2) ≤ K*B*X^(-δ) := by
  obtain ⟨δ,K,hδ,hK,hbound⟩ := sparse_stopped_beta_energy (ι := ι) (η := 1/50)
    hpnt hC (by norm_num) hξ hξz
  refine ⟨δ,K,hδ,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with X hbound hX
  intro B ρ hB hBX hρ hρ₂ j k h hboundary S W R D U hS hW hR hD hU
  apply hbound B (X^(38/100:ℝ)) (X^(36/100:ℝ)) hB hBX
    (Real.rpow_pos_of_pos hX _) ((ordinary_late_threshold_ratio hX).ge)
    S W R D U (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k h hS hW hR
    (fun d hd => (hD d hd).1) _ _ hU
  · intro d hd p hp
    have hpp := (primaryPrimeFactor_spec (hD d hd).1 hp).1
    have hpX := (norm_le_of_dvd (primary_ne_zero (hD d hd).1)
      (primaryPrimeFactor_spec (hD d hd).1 hp).2).trans (hD d hd).2
    exact ⟨zero_lt_one.trans (geometricBinLower_gt_one hρ
      (geometricPrimeBin_index hρ hρ₂ hpp hpX)),(geometricPrimeBin_cell hρ hρ₂ hpp hpX).1⟩
  · intro d hd p hp hbin
    have hpp := (primaryPrimeFactor_spec (hD d hd).1 hp).1
    have hpX := (norm_le_of_dvd (primary_ne_zero (hD d hd).1)
      (primaryPrimeFactor_spec (hD d hd).1 hp).2).trans (hD d hd).2
    exact geometric_late_prime_bound hρ hρ₂ hboundary hpp hpX hbin

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseStoppedBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual sparse late-stop Gauss sums have a power saving. The two
coefficient energies come from their literal stopping constructions;
the smooth factor is handled by the proved weighted cubic sieve. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma energy_bounded_twist (S : Finset Eisenstein)
    (α v : Eisenstein → ℂ) (hv : ∀ a ∈ S, ‖v a‖ ≤ 1) :
    (∑ a ∈ S, ‖α a*v a‖^2) ≤ ∑ a ∈ S, ‖α a‖^2 := by
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_of_le_one_right (_root_.norm_nonneg _) (hv a ha)) 2

/-- Fixed support dilations and arbitrary bounded independent twists are
allowed. The small-prime boundary and the stopping thresholds are the
actual geometric ones, not assumed sparsity of an abstract coefficient. -/
theorem ordinary_late_stopped_bilinear
    {ι γ : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ M : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hM : 1 ≤ M)
    {G : γ → ℝ → ℂ} (hG : UniformLogWeights G) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ V : ℝ), Real.exp 1 ≤ A → 1 ≤ B → A ≤ X → B ≤ X →
      A ≤ M*X^(2/3:ℝ) → B ≤ M*X^(2/3:ℝ) → A*B ≤ M*X →
      1 < ρ → ρ ≤ 2 → 0 < V →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop)
        (vα vβ : Eisenstein → ℂ) (w : Eisenstein → γ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ norm b ≤ B) →
      (∀ a ∈ P, ‖vα a‖ ≤ 1) → (∀ b ∈ Q, ‖vβ b‖ ≤ 1) →
      ‖∑ a ∈ P, ∑ b ∈ Q,
        (stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining a*vα a)*
        (stoppedBeta R D
          (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
          primeDetectorCutoff (X^ξ)
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b*vβ b)*
        gauss (a*b)*G (w a) (norm b/V)‖ ≤ K*X^(5/6-τ) := by
  obtain ⟨δ,Kβ,hδ,hKβ,hβ⟩ := ordinary_late_stopped_energy (ι := ι) hpnt hC hξ hξz
  obtain ⟨Kα,d,hKα,hα⟩ := smallB_stopped_alpha_energy hpnt
  obtain ⟨Ks,hKs,hsieve⟩ := hG.metaplectic_weighted_bilinear
    (show 0 < δ/4 by positivity)
  obtain ⟨H,hH,hlog⟩ := log_power_normalization_bound d (show 0 < δ/4 by positivity)
  let K₀ := Ks*(3*Kα*Kβ*(H+1)*M^(2+δ/4))
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  refine ⟨δ/4,Real.sqrt K₀,by positivity,Real.sqrt_pos.mpr hK₀,?_⟩
  filter_upwards [hβ,eventually_ge_atTop (1:ℝ)] with X hβ hX
  intro A B ρ V hA hB hAX hBX hAs hBs hAB hρ hρ₂ hV j k h hboundary
    S W R D E U P Q remaining vα vβ w hS hW hR hD hE hP hQ hvα hvβ
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hA1 : 1 ≤ A := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)).trans hA
  let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
  let β := stoppedBeta R D
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
  have hea : (∑ a ∈ P, ‖α a*vα a‖^2) ≤ Kα*A*(1+Real.log X)^d := by
    apply (energy_bounded_twist P α vα hvα).trans
    apply (hα E U P primeDetectorCutoff (X^ξ) A remaining hE
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) hA hP).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hKα.le (by linarith))
    have hl : 1+Real.log A ≤ 1+Real.log X := by
      linarith [Real.log_le_log (show 0 < A from zero_lt_one.trans_le hA1) hAX]
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hA1]) hl d
  have heb : (∑ b ∈ Q, ‖β b*vβ b‖^2) ≤ Kβ*B*X^(-δ) :=
    (energy_bounded_twist Q β vβ hvβ).trans
      (hβ B ρ (by linarith) hBX hρ hρ₂ j k h hboundary S W R D Q hS hW hR hD hQ)
  have hL : 0 ≤ (1+Real.log X)^d := pow_nonneg (by linarith [Real.log_nonneg hX]) _
  have hsq : ‖∑ a ∈ P, ∑ b ∈ Q,
      (α a*vα a)*(β b*vβ b)*gauss (a*b)*G (w a) (norm b/V)‖^2 ≤
      K₀*X^(5/3-δ/2) := by
    apply (hsieve w P Q A B V hA1 hB hV hP hQ
      (fun a => α a*vα a) (fun b => β b*vβ b)).trans
    calc
      _ ≤ Ks*(A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
          (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ)) := by gcongr
      _ = Ks*((A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
          (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ))) := by ring
      _ ≤ Ks*((3*Kα*Kβ*(H+1)*M^(2+δ/4))*X^(5/3-δ/2)) :=
        mul_le_mul_of_nonneg_left (sparse_bilinear_power_bound hX (by linarith)
          (by linarith) hM hδ (by positivity) hKα.le hKβ.le d hAs hBs hAB
          ((hlog X hX).trans (by linarith))) hKs.le
      _ = _ := by dsimp [K₀]; ring
  have he : (Real.sqrt K₀*X^(5/6-δ/4))^2 = K₀*X^(5/3-δ/2) := by
    rw [mul_pow,Real.sq_sqrt hK₀.le,←Real.rpow_mul_natCast hXp.le]
    congr 2
    ring
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp (hsq.trans_eq he.symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseProductEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sparse Gauss contribution with the manuscript's literal smooth
product envelope. The envelope is not replaced by independent factors. -/
noncomputable section
open Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem ordinary_late_stopped_product_envelope
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ M D : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hM : 1 ≤ M) (hD : 1 ≤ D)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ : ℝ), 0 < A → Real.exp 1 ≤ M*A → 1 ≤ B →
      M*A ≤ X → B ≤ X → M*A ≤ D*X^(2/3:ℝ) → B ≤ D*X^(2/3:ℝ) →
      (M*A)*B ≤ D*X → 1 < ρ → ρ ≤ 2 →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R F E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop)
        (vα vβ : Eisenstein → ℂ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ F, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ M*A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ norm b ≤ B) →
      (∀ a ∈ P, ‖vα a‖ ≤ 1) → (∀ b ∈ Q, ‖vβ b‖ ≤ 1) →
      ‖∑ a ∈ P, ∑ b ∈ Q,
        (stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining a*vα a)*
        (stoppedBeta R F
          (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
          primeDetectorCutoff (X^ξ)
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b*vβ b)*
        gauss (a*b)*V (norm (a*b)/X)‖ ≤ K*X^(5/6-τ) := by
  let hW := uniformLogWeights_constant (ι := Unit) V hV hpos hsm
  let hG := hW.logDilate (Real.log M) (Real.log_nonneg hM)
  obtain ⟨τ,K,hτ,hK,hbound⟩ := ordinary_late_stopped_bilinear (ι := ι)
    hpnt hC hξ hξz hD hG
  refine ⟨τ,K,hτ,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with X hbound hX
  intro A B ρ hA hMA hB hAX hBX hAs hBs hAB hρ hρ₂ j k h hboundary
    S W R F E U P Q remaining vα vβ hS hWeights hR hF hE hP hQ hvα hvβ
  let w : Eisenstein → Unit × {s : ℝ // 0 < s ∧ |Real.log s| ≤ Real.log M} := fun a =>
    ((),if ha : a ∈ P then
      ⟨norm a/A,log_dyad_ratio hA hM (hP a ha).2.2.1 (hP a ha).2.2.2⟩
      else ⟨1,by simp [Real.log_nonneg hM]⟩)
  have he (a : Eisenstein) (ha : a ∈ P) (b : Eisenstein) :
      V ((w a).2*(norm b/(X/A))) = V (norm (a*b)/X) := by
    dsimp only [w]
    simp only [ha,dite_eq_left,Subtype.coe_mk]
    congr 1
    rw [norm_mul_eq]
    field_simp
  have hb := hbound (M*A) B ρ (X/A) hMA hB hAX hBX hAs hBs hAB hρ hρ₂
    (div_pos hX hA) j k h hboundary S W R F E U P Q remaining vα vβ w
    hS hWeights hR hF hE
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2⟩) hQ hvα hvβ
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [he a ha b]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionModelEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal model polynomial has the expected energy bound on a
norm annulus. This retains the logarithmic coefficient complexity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma dispersionModel_norm_sq_le (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) {L : ℝ} (hL : 0 < L) (hS : ∀ b ∈ S, L ≤ norm b) :
    ‖dispersionModel S β u‖^2 ≤
      (S.card:ℝ)*L^(-(1/3:ℝ))*(∑ b ∈ S, ‖β b‖^2) := by
  let f : Eisenstein → ℂ := fun b => normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)
  have hf (b : Eisenstein) (hb : b ∈ S) : ‖f b‖^2 ≤ L^(-(1/3:ℝ)) := by
    have hp : 0 < norm b := hL.trans_le (hS b hb)
    dsimp [f]
    rw [norm_mul,norm_normTwist,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hp _)]
    calc
      _ ≤ (L^(-1/6:ℝ))^2 := pow_le_pow_left₀ (by positivity)
        (Real.rpow_le_rpow_of_nonpos hL (hS b hb) (by norm_num)) 2
      _ = _ := by rw [←Real.rpow_natCast (L^(-1/6:ℝ)) 2,←Real.rpow_mul hL.le]; norm_num
  have he : dispersionModel S β u = ∑ b ∈ S, β b*f b := by
    unfold dispersionModel f
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [he]
  apply (complex_bilinear_rows_sq S β f).trans
  have hh : (∑ b ∈ S, ‖f b‖^2) ≤ (S.card:ℝ)*L^(-(1/3:ℝ)) := by
    simpa using Finset.sum_le_sum hf
  exact (mul_le_mul_of_nonneg_left hh (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans_eq
    (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAbsoluteModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute model mass controls both the model and the coprimality error
in its Type-I replacement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma dispersionAbsoluteModel_nonneg (S : Finset Eisenstein) (β : Eisenstein → ℂ) :
    0 ≤ dispersionAbsoluteModel S β :=
  Finset.sum_nonneg (fun b _ => mul_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (norm_nonneg b) _))

lemma dispersionAbsoluteModel_sq_le (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {L : ℝ} (hL : 0 < L) (hS : ∀ b ∈ S, L ≤ norm b) :
    (dispersionAbsoluteModel S β)^2 ≤
      (S.card:ℝ)*L^(-(1/3:ℝ))*(∑ b ∈ S, ‖β b‖^2) := by
  have he : dispersionModel S (fun b => (‖β b‖:ℂ)) 0 = (dispersionAbsoluteModel S β:ℂ) := by
    unfold dispersionModel dispersionAbsoluteModel
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [normTwist,zero_mul,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,
      Complex.ofReal_mul]
  have hh := dispersionModel_norm_sq_le S (fun b => (‖β b‖:ℂ)) 0 hL hS
  simpa only [he,Complex.norm_real,Real.norm_eq_abs,sq_abs,abs_norm] using hh


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseModelCounting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct sparse-branch model counting. Mutual coprimality is not
removed: the original squarefree product factor remains in the sum. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma squarefree_model_bilinear_counting
    (P Q : Finset Eisenstein) (α β : Eisenstein → ℂ) (V : Eisenstein → Eisenstein → ℂ)
    {A B L₁ L₂ H : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (_hH : 0 ≤ H)
    (hP : ∀ a ∈ P, primary a ∧ L₁ ≤ norm a ∧ norm a ≤ A)
    (hQ : ∀ b ∈ Q, primary b ∧ L₂ ≤ norm b ∧ norm b ≤ B)
    (hV : ∀ a ∈ P, ∀ b ∈ Q, ‖V a b‖ ≤ H) :
    ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
      ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖^2 ≤
      (324*H^2)*(A*B)*L₁^(-1/3:ℝ)*L₂^(-1/3:ℝ)*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by
  have hcardP : (P.card:ℝ) ≤ 18*A := by
    apply (Nat.cast_le.mpr (Finset.card_le_card (show P ⊆ primaryElementBall A from ?_))).trans
      (primaryElementBall_card_le hA)
    intro a ha
    exact mem_primaryElementBall.mpr ⟨(hP a ha).1,(hP a ha).2.2⟩
  have hcardQ : (Q.card:ℝ) ≤ 18*B := by
    apply (Nat.cast_le.mpr (Finset.card_le_card (show Q ⊆ primaryElementBall B from ?_))).trans
      (primaryElementBall_card_le hB)
    intro b hb
    exact mem_primaryElementBall.mpr ⟨(hQ b hb).1,(hQ b hb).2.2⟩
  have hnorm :
      ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
        ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖ ≤
      H*dispersionAbsoluteModel P α*dispersionAbsoluteModel Q β := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ a ∈ P, H*(‖α a‖*norm a^(-1/6:ℝ))*
          dispersionAbsoluteModel Q β := by
        apply Finset.sum_le_sum
        intro a ha
        apply (norm_sum_le _ _).trans
        rw [dispersionAbsoluteModel,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro b hb
        have hna := norm_nonneg a
        have hnb := norm_nonneg b
        have hμ : ‖(idealMoebius (a*b):ℂ)^2‖ ≤ 1 := by
          simpa only [norm_pow,one_pow] using
            pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_idealMoebius_le_one (a*b)) 2
        rw [norm_mul,norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),norm_mul_eq,
          Real.mul_rpow (norm_nonneg a) (norm_nonneg b)]
        calc
          _ ≤ ‖α a‖*‖β b‖*1*(norm a^(-1/6:ℝ)*norm b^(-1/6:ℝ))*H := by
            gcongr
            exact hV a ha b hb
          _ = _ := by ring
      _ = _ := by rw [←Finset.sum_mul,←Finset.mul_sum]; rfl
  have heP := dispersionAbsoluteModel_sq_le P α hL₁ (fun a ha => (hP a ha).2.1)
  have heQ := dispersionAbsoluteModel_sq_le Q β hL₂ (fun b hb => (hQ b hb).2.1)
  have hp : 0 ≤ dispersionAbsoluteModel P α := dispersionAbsoluteModel_nonneg _ _
  have hq : 0 ≤ dispersionAbsoluteModel Q β := dispersionAbsoluteModel_nonneg _ _
  calc
    _ ≤ (H*dispersionAbsoluteModel P α*dispersionAbsoluteModel Q β)^2 :=
      pow_le_pow_left₀ (_root_.norm_nonneg _) hnorm 2
    _ = H^2*(dispersionAbsoluteModel P α)^2*(dispersionAbsoluteModel Q β)^2 := by ring
    _ ≤ H^2*((P.card:ℝ)*L₁^(-1/3:ℝ)*(∑ a ∈ P, ‖α a‖^2))*
        ((Q.card:ℝ)*L₂^(-1/3:ℝ)*(∑ b ∈ Q, ‖β b‖^2)) := by
      gcongr
      · simpa only [neg_div] using heP
      · simpa only [neg_div] using heQ
    _ ≤ H^2*((18*A)*L₁^(-1/3:ℝ)*(∑ a ∈ P, ‖α a‖^2))*
        ((18*B)*L₂^(-1/3:ℝ)*(∑ b ∈ Q, ‖β b‖^2)) := by gcongr
    _ = _ := by ring

lemma sparse_model_counting_scale {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 0 < M) :
    (A*B)*(A/M)^(-1/3:ℝ)*(B/M)^(-1/3:ℝ) = M^(2/3:ℝ)*(A*B)^(2/3:ℝ) := by
  rw [Real.div_rpow hA.le hM.le,Real.div_rpow hB.le hM.le,
    Real.mul_rpow hA.le hB.le]
  have ha : A*A^(-1/3:ℝ) = A^(2/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one A]
    rw [←Real.rpow_add hA]
    norm_num
  have hb : B*B^(-1/3:ℝ) = B^(2/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one B]
    rw [←Real.rpow_add hB]
    norm_num
  have hm : M^(-1/3:ℝ)*M^(-1/3:ℝ) = M^(-2/3:ℝ) := by
    rw [←Real.rpow_add hM]
    norm_num
  calc
    (A*B)*(A^(-1/3:ℝ)/M^(-1/3:ℝ))*(B^(-1/3:ℝ)/M^(-1/3:ℝ)) =
        (A*A^(-1/3:ℝ))*(B*B^(-1/3:ℝ))/(M^(-1/3:ℝ)*M^(-1/3:ℝ)) := by ring
    _ = (A^(2/3:ℝ)*B^(2/3:ℝ))/M^(-2/3:ℝ) := by rw [ha,hb,hm]
    _ = M^(2/3:ℝ)*(A^(2/3:ℝ)*B^(2/3:ℝ)) := by
      rw [show (-2/3:ℝ) = -(2/3) by ring,Real.rpow_neg hM.le,div_inv_eq_mul,mul_comm]

/-- The squarefree model has at most the cubic-sieve shape by direct
finite counting. No cancellation or model asymptotic is assumed. -/
lemma squarefree_model_bilinear_operator
    (P Q : Finset Eisenstein) (α β : Eisenstein → ℂ) (V : Eisenstein → Eisenstein → ℂ)
    {A B M H ε : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hM : 0 < M)
    (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hP : ∀ a ∈ P, primary a ∧ A/M ≤ norm a ∧ norm a ≤ A)
    (hQ : ∀ b ∈ Q, primary b ∧ B/M ≤ norm b ∧ norm b ≤ B)
    (hV : ∀ a ∈ P, ∀ b ∈ Q, ‖V a b‖ ≤ H) :
    ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
      ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖^2 ≤
      (324*H^2*M^(2/3:ℝ))*(A*B)^ε*(A+B+(A*B)^(2/3:ℝ))*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hpref : 1 ≤ (A*B)^ε := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hA hB) hε
  have hshape : (A*B)^(2/3:ℝ) ≤ (A*B)^ε*(A+B+(A*B)^(2/3:ℝ)) := by
    calc
      _ ≤ A+B+(A*B)^(2/3:ℝ) := by linarith
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hpref
  apply (squarefree_model_bilinear_counting P Q α β V hAp.le hBp.le
    (div_pos hAp hM) (div_pos hBp hM) hH hP hQ hV).trans
  calc
    _ = (324*H^2*M^(2/3:ℝ))*(A*B)^(2/3:ℝ)*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by
      have hh := sparse_model_counting_scale hAp hBp hM
      calc
        _ = (324*H^2)*((A*B)*(A/M)^(-1/3:ℝ)*(B/M)^(-1/3:ℝ))*
            (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by ring
        _ = _ := by rw [hh]; ring
    _ ≤ (324*H^2*M^(2/3:ℝ))*((A*B)^ε*(A+B+(A*B)^(2/3:ℝ)))*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ Q, ‖β b‖^2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hshape (by positivity))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseStoppedModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual late-stop squarefree model is power-saving by direct
counting and the two proved coefficient energies. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem ordinary_late_stopped_model
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ M H : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hM : 1 ≤ M) (hH : 0 ≤ H) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ : ℝ), Real.exp 1 ≤ A → 1 ≤ B → A ≤ X → B ≤ X →
      A ≤ M*X^(2/3:ℝ) → B ≤ M*X^(2/3:ℝ) → A*B ≤ M*X →
      1 < ρ → ρ ≤ 2 →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop)
        (V : Eisenstein → Eisenstein → ℂ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A/2 ≤ norm a ∧ norm a ≤ A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B) →
      (∀ a ∈ P, ∀ b ∈ Q, ‖V a b‖ ≤ H) →
      ‖∑ a ∈ P, ∑ b ∈ Q,
        stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining a*
        stoppedBeta R D
          (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
          primeDetectorCutoff (X^ξ)
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b*
        (idealMoebius (a*b):ℂ)^2*((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖ ≤
        K*X^(5/6-τ) := by
  obtain ⟨δ,Kβ,hδ,hKβ,hβ⟩ := ordinary_late_stopped_energy (ι := ι) hpnt hC hξ hξz
  obtain ⟨Kα,d,hKα,hα⟩ := smallB_stopped_alpha_energy hpnt
  obtain ⟨J,hJ,hlog⟩ := log_power_normalization_bound d (show 0 < δ/4 by positivity)
  let Ks : ℝ := 1+324*H^2*(2:ℝ)^(2/3:ℝ)
  have hKs : 0 < Ks := by dsimp [Ks]; positivity
  let K₀ := Ks*(3*Kα*Kβ*(J+1)*M^(2+δ/4))
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  refine ⟨δ/4,Real.sqrt K₀,by positivity,Real.sqrt_pos.mpr hK₀,?_⟩
  filter_upwards [hβ,eventually_ge_atTop (1:ℝ)] with X hβ hX
  intro A B ρ hA hB hAX hBX hAs hBs hAB hρ hρ₂ j k h hboundary
    S W R D E U P Q remaining V hS hW hR hD hE hP hQ hV
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hA1 : 1 ≤ A := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)).trans hA
  let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
  let β := stoppedBeta R D
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
  have hea : (∑ a ∈ P, ‖α a‖^2) ≤ Kα*A*(1+Real.log X)^d := by
    apply (hα E U P primeDetectorCutoff (X^ξ) A remaining hE
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) hA
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2⟩)).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hKα.le (by linarith))
    have hl : 1+Real.log A ≤ 1+Real.log X := by
      linarith [Real.log_le_log (show 0 < A from zero_lt_one.trans_le hA1) hAX]
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hA1]) hl d
  have heb : (∑ b ∈ Q, ‖β b‖^2) ≤ Kβ*B*X^(-δ) :=
    hβ B ρ (by linarith) hBX hρ hρ₂ j k h hboundary S W R D Q hS hW hR hD
      (fun b hb => ⟨(hQ b hb).1,(hQ b hb).2.1,(hQ b hb).2.2.2⟩)
  have hL : 0 ≤ (1+Real.log X)^d := pow_nonneg (by linarith [Real.log_nonneg hX]) _
  have hsieve := squarefree_model_bilinear_operator P Q α β V hA1 hB
    (by norm_num : (0:ℝ) < 2) hH (show 0 ≤ δ/4 by positivity)
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2⟩)
    (fun b hb => ⟨(hQ b hb).1,(hQ b hb).2.2⟩) hV
  have hsq : ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
      ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖^2 ≤ K₀*X^(5/3-δ/2) := by
    apply hsieve.trans
    calc
      _ ≤ Ks*(A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
          (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ)) := by
        dsimp only [Ks]
        gcongr
        linarith
      _ = Ks*((A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
          (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ))) := by ring
      _ ≤ Ks*((3*Kα*Kβ*(J+1)*M^(2+δ/4))*X^(5/3-δ/2)) :=
        mul_le_mul_of_nonneg_left (sparse_bilinear_power_bound hX (by linarith)
          (by linarith) hM hδ (by positivity) hKα.le hKβ.le d hAs hBs hAB
          ((hlog X hX).trans (by linarith))) hKs.le
      _ = _ := by dsimp [K₀]; ring
  have he : (Real.sqrt K₀*X^(5/6-δ/4))^2 = K₀*X^(5/3-δ/2) := by
    rw [mul_pow,Real.sq_sqrt hK₀.le,←Real.rpow_mul_natCast hXp.le]
    congr 2
    ring
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp (hsq.trans_eq he.symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseCenteredBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered sparse late-stop contribution.
Both its Gauss part and its squarefree model are proved small; the
norm range supplies the cubic-sieve geometry. -/
noncomputable section
open Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem ordinary_sparse_centered_bilinear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ D : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hD : 1 ≤ D)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ : ℝ), 0 < A → Real.exp 1 ≤ 2*A →
      X^(35/100:ℝ) ≤ B → B ≤ X^(40/100:ℝ) → 2*A ≤ D*X/B →
      1 < ρ → ρ ≤ 2 →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R F E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop)
        (vα vβ : Eisenstein → ℂ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ F, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B) →
      (∀ a ∈ P, ‖vα a‖ ≤ 1) → (∀ b ∈ Q, ‖vβ b‖ ≤ 1) →
      ‖∑ a ∈ P, ∑ b ∈ Q,
        (stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining a*vα a)*
        (stoppedBeta R F
          (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
          primeDetectorCutoff (X^ξ)
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b*vβ b)*
        centeredGauss (a*b)*V (norm (a*b)/X)‖ ≤ K*X^(5/6-τ) := by
  obtain ⟨τg,Kg,hτg,hKg,hGauss⟩ := ordinary_late_stopped_product_envelope (ι := ι)
    hpnt hC hξ hξz (by norm_num : (1:ℝ) ≤ 2) hD V hV hpos hsm
  obtain ⟨H,hH,hVbound⟩ := (uniformLogWeights_constant (ι := Unit) V hV hpos hsm).norm_bound
  obtain ⟨τm,Km,hτm,hKm,hModel⟩ := ordinary_late_stopped_model (ι := ι)
    hpnt hC hξ hξz hD hH
  have hcs := cStar_pos
  refine ⟨min τg τm,Kg+cStar*Km,lt_min hτg hτm,by positivity,?_⟩
  filter_upwards [hGauss,hModel,eventually_late_stop_rectangle_bounds hD,
    eventually_ge_atTop (1:ℝ)] with X hGauss hModel hrect hX
  intro A B ρ hA h2A hBlo hBhi hAB hρ hρ₂ j k h hboundary
    S W R F E U P Q remaining vα vβ hS hW hR hF hE hP hQ hvα hvβ
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 35/100)).trans hBlo
  obtain ⟨hAX,hBX,hAs,hBs,hABs⟩ := hrect (2*A) B hBlo hBhi hAB
  let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
  let β := stoppedBeta R F
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
  let Gs := ∑ a ∈ P, ∑ b ∈ Q, (α a*vα a)*(β b*vβ b)*gauss (a*b)*V (norm (a*b)/X)
  let Ws := fun a b => vα a*vβ b*V (norm (a*b)/X)
  let Ms := ∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
    ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*Ws a b
  have hg : ‖Gs‖ ≤ Kg*X^(5/6-τg) := hGauss A B ρ hA h2A hB1 hAX hBX
    hAs hBs hABs hρ hρ₂ j k h hboundary S W R F E U P Q remaining vα vβ
    hS hW hR hF hE hP (fun b hb => ⟨(hQ b hb).1,(hQ b hb).2.1,(hQ b hb).2.2.2⟩) hvα hvβ
  have hWs : ∀ a ∈ P, ∀ b ∈ Q, ‖Ws a b‖ ≤ H := by
    intro a ha b hb
    dsimp [Ws]
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 1*1*H := mul_le_mul (mul_le_mul (hvα a ha) (hvβ b hb)
        (_root_.norm_nonneg _) (by norm_num)) (hVbound () _) (_root_.norm_nonneg _) (by norm_num)
      _ = H := by ring
  have hm : ‖Ms‖ ≤ Km*X^(5/6-τm) := hModel (2*A) B ρ h2A hB1 hAX hBX
    hAs hBs hABs hρ hρ₂ j k h hboundary S W R F E U P Q remaining Ws
    hS hW hR hF hE
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,by linarith [(hP a ha).2.2.1],(hP a ha).2.2.2⟩)
    hQ hWs
  have he : (∑ a ∈ P, ∑ b ∈ Q, (α a*vα a)*(β b*vβ b)*centeredGauss (a*b)*
      V (norm (a*b)/X)) = Gs-(cStar:ℂ)*Ms := by
    dsimp only [Gs,Ms]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [centeredGauss,Ws]
    ring
  change ‖∑ a ∈ P, ∑ b ∈ Q, (α a*vα a)*(β b*vβ b)*centeredGauss (a*b)*
    V (norm (a*b)/X)‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖Gs‖+‖(cStar:ℂ)*Ms‖ := norm_sub_le _ _
    _ ≤ Kg*X^(5/6-τg)+cStar*(Km*X^(5/6-τm)) := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos]
      exact add_le_add hg (mul_le_mul_of_nonneg_left hm cStar_pos.le)
    _ ≤ Kg*X^(5/6-min τg τm)+cStar*(Km*X^(5/6-min τg τm)) := by
      gcongr
      · exact min_le_left τg τm
      · exact min_le_right τg τm
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseKernelTwists
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sparse centered estimate applies to the original common norm
and angular twists by exact multiplicativity, with no height restriction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma sparse_common_twist_norm {a : Eisenstein} (ha : primary a) (ℓ : ℤ) (u : ℝ) :
    ‖theta ℓ a*normTwist u a‖ = 1 := by
  rw [norm_mul,norm_theta (primary_ne_zero ha),norm_normTwist,mul_one]

lemma sparse_common_twist_identity (P Q : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hQ : ∀ b ∈ Q, primary b)
    (α β F V : Eisenstein → ℂ) (ℓ : ℤ) (u : ℝ) :
    (∑ a ∈ P, ∑ b ∈ Q, α a*β b*F (a*b)*theta ℓ (a*b)*normTwist u (a*b)*V (a*b)) =
    ∑ a ∈ P, ∑ b ∈ Q,
      (α a*(theta ℓ a*normTwist u a))*(β b*(theta ℓ b*normTwist u b))*F (a*b)*V (a*b) := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [theta_mul,normTwist_mul u (primary_ne_zero (hP a ha)) (primary_ne_zero (hQ b hb))]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseLowKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual low-height sparse late-stop cancellation. The common angular
and norm twists are placed on the two independent coefficient sides. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem ordinary_sparse_low_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ D : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hD : 1 ≤ D) (Ct : ℕ) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ H : ℝ) (ℓ : ℤ), 0 < A → Real.exp 1 ≤ 2*A →
      X^(35/100:ℝ) ≤ B → B ≤ X^(40/100:ℝ) → 2*A ≤ D*X/B →
      1 < ρ → ρ ≤ 2 → 0 < H →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R F E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ F, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B) →
      let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
      let β := stoppedBeta R F
        (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
        primeDetectorCutoff (X^ξ)
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
      ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b)‖ ≤
        K*(1+Real.log X)^Ct*X^(5/6-τ) := by
  obtain ⟨τ,K,hτ,hK,hbound⟩ := ordinary_sparse_centered_bilinear (ι := ι)
    hpnt hC hξ hξz hD primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth
  refine ⟨τ,(8/3)*Real.log 2*K,hτ,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hbound hX
  intro A B ρ H ℓ hA h2A hBlo hBhi hAB hρ hρ₂ hH j k h hboundary
    S W R F E U P Q remaining hS hW hR hF hE hP hQ
  dsimp only
  let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
  let β := stoppedBeta R F
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
  let T := (1+Real.log X)^Ct
  have hT : 0 < T := by dsimp [T]; positivity [Real.log_nonneg hX]
  have hM : 0 ≤ K*X^(5/6-τ) := by positivity
  have hb (t : ℝ) : ‖centeredProductSmoothed P Q α β ℓ primeProductEnvelope X t‖ ≤
      K*X^(5/6-τ) := by
    have he := hbound A B ρ hA h2A hBlo hBhi hAB hρ hρ₂ j k h hboundary
      S W R F E U P Q remaining (fun a => theta ℓ a*normTwist t a)
      (fun b => theta ℓ b*normTwist t b) hS hW hR hF hE hP hQ
      (fun a ha => (sparse_common_twist_norm (hP a ha).1 ℓ t).le)
      (fun b hb => (sparse_common_twist_norm (hQ b hb).1 ℓ t).le)
    rw [←sparse_common_twist_identity P Q (fun a ha => (hP a ha).1)
      (fun b hb => (hQ b hb).1) α β centeredGauss
      (fun n => primeProductEnvelope (norm n/X)) ℓ t] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [centered_product_low_integral P Q α β ℓ primeProductEnvelope X X T hH]
  have heint : (fun t => (lowHeightWeight H T t*Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*
      centeredProductSmoothed P Q α β ℓ primeProductEnvelope X t) =
      (fun t => lowHeightWeight H T t*(Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*
        centeredProductSmoothed P Q α β ℓ primeProductEnvelope X t)) := by funext t; ring
  rw [heint]
  have hi := lowHeightWeight_integral_bound H hT hM
    (fun t => Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*
      centeredProductSmoothed P Q α β ℓ primeProductEnvelope X t) (by
        intro t _
        rw [norm_mul]
        have hephase : ‖Complex.exp ((-Real.log X*t:ℝ)*Complex.I)‖ = 1 := by
          simp only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
            Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,Real.exp_zero]
        rw [hephase,one_mul]
        exact hb t)
  exact hi.trans_eq (by dsimp [T]; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularScaleFirstStoppedLate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal late scale-first stopped dyad has a power saving. The
actual coefficient, failed-prefix condition and product cutoff are first
transported exactly, then the proved sparse low-height estimate applies. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_distinguishedStoppedLate_bound (ℓ : ℤ) (i : ℕ) (hpnt : PrimaryPrimePNT)
    {C ξ ρ ε : ℝ} (hC : 0 < C) (hξ : 0 < ξ)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hgap : ξ+ε < 1/100) (Ct : ℕ) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H : ℝ), 0 < H → ∀ h : ℕ,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h →
      ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h ≤ (Real.log X)^C →
      ∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ) (j k : ℕ), 1 ≤ q.2.1 →
      ‖angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h false d q j k‖ ≤
        K*(1+Real.log X)^Ct*X^(5/6-τ) := by
  have hξz : ξ ≤ 2/5 := by linarith
  obtain ⟨τ,K,hτ,hK,hsparse⟩ := ordinary_sparse_low_kernel (ι := Fin i)
    hpnt hC hξ hξz (show (1:ℝ) ≤ 32 by norm_num) Ct
  obtain ⟨V,_hV,hweights⟩ := distinguishedStoppingWeights_uniform
  refine ⟨τ,K,hτ,hK,?_⟩
  filter_upwards [hsparse,eventually_angular_distinguishedStoppedDyad_geometry ℓ hρ hρ₂ hε hsmall hgap,
    eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 38/100)).eventually_ge_atTop 2,
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 1) (8*Real.exp 1)]
    with X hsparse hgeom hX hZ hlong
  intro H hH h hh hboundary d q j k hk
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  by_cases hn : angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h false d q j k = 0
  · rw [hn,norm_zero]
    positivity
  obtain ⟨hBlo,hBhi,hBX,hprodlo,hprodhi,hq⟩ := hgeom i Ct H h false d q j k hk hn
  let A := stoppedNormDyadLength j/2
  let B := stoppedNormDyadLength k
  let Δ := geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X
  have hAp : 0 < A := by dsimp [A]; positivity [stoppedNormDyadLength_pos j]
  have hBp : 0 < B := stoppedNormDyadLength_pos k
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  have h2A : Real.exp 1 ≤ 2*A := by
    have hbb : 8*Real.exp 1*B ≤ X := by
      have he := mul_le_mul_of_nonneg_left hBhi (by positivity : 0 ≤ 8*Real.exp 1)
      exact he.trans (by simpa only [Real.rpow_one] using hlong)
    have hm : Real.exp 1*B ≤ (2*A)*B := by
      change X/16 ≤ A*B at hprodlo
      nlinarith
    apply (mul_le_mul_iff_right₀ hBp).mp
    simpa only [mul_comm] using hm
  have hB35 : X^(35/100:ℝ) ≤ B := by
    norm_num only [show (35/100:ℝ) = 7/20 by norm_num]
    exact hBlo
  have hB40 : B ≤ X^(40/100:ℝ) := hBhi.trans
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))
  have hAB : 2*A ≤ 32*X/B := by
    apply (le_div_iff₀ hBp).mpr
    change A*B ≤ 16*X at hprodhi
    nlinarith
  have hbnd : ρ*geometricBinLower ρ X (h-Δ) ≤ (Real.log X)^C := by
    have he := geometricBinLower_shift hρ hXp hXF (h-Δ)
    rw [Nat.sub_add_cancel hh] at he
    simpa only [he] using hboundary
  have hP (a : Eisenstein) (ha : a ∈ stoppedNormDyad (distinguishedStoppedSide X) j) :
      primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A := by
    have hp := distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1
    have hr := stoppedNormDyad_outer_bounds ha hp.1
    exact ⟨hp.1,hp.2.1,hr.1,by dsimp [A]; nlinarith [hr.2]⟩
  have hQ (b : Eisenstein) (hb : b ∈ stoppedIntervalSupport (Fin i) X (B/2) B 1) :
      primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B := by
    have hp := stoppedIntervalSupport_spec X (B/2) B 1 hb
    exact ⟨hp.1,hp.2.1,(Finset.mem_filter.mp hb).2.2.2.1.le,hp.2.2⟩
  have he := hsparse A B ρ H ℓ hAp h2A hB35 hB40 hAB hρ hρ₂ hH
    (q.1-Δ) q.2.1 (h-Δ) hbnd
    (fun _ : Fin i => primeCutoff X) (fun a p => distinguishedStoppingWeights d a (norm p))
    (orderedConvolutionSupport (fun _ : Fin i => primeCutoff X)) (primaryElementBall X)
    (centralPrimaryFactors X) (centralPrimaryFactors X)
    (stoppedNormDyad (distinguishedStoppedSide X) j)
    (stoppedIntervalSupport (Fin i) X (B/2) B 1)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      q.1 q.2.2)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1)
    (fun a p _ => (hweights i _ d).1 a (norm p))
    (fun _ hr => orderedPrimarySupport_primary _
      (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr)
    (fun _ hd => mem_primaryElementBall.mp hd)
    (fun _ he => (mem_primaryElementBall.mp he).1) hP hQ
  rw [angular_distinguishedStoppedDyad_to_row ℓ i hρ hρ₂ hX Ct H h false d q j k hk
    (by simpa only [Bool.false_eq_true,ite_false, if_false] using hZ) hBX hq hh]
  simpa only [B,Δ,distinguishedStoppedAlpha,stoppedRowCoefficient,distinguishedShiftedSideTest,
    show (36/100:ℝ) = 9/25 by norm_num,
    Bool.false_eq_true,ite_false, if_false,normTwist,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one]
    using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularScaleFirstLateNegligible
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite collection of actual late stopped arities is negligible;
the powers of logarithms from every finite partition are absorbed. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_scaleFirstStoppedLate_isLittleO_oai (ℓ : ℤ) (m : ℕ) (hpnt : PrimaryPrimePNT)
    {C ξ ρ ε : ℝ} (hC : 0 < C) (hξ : 0 < ξ)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hgap : ξ+ε < 1/100) (Ct : ℕ) (H : ℝ → ℝ) (h : ℝ → ℕ)
    (hH : ∀ᶠ X : ℝ in atTop, 0 < H X)
    (hh : ∀ᶠ X : ℝ in atTop,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X)
    (hboundary : ∀ᶠ X : ℝ in atTop,
      ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X) ≤ (Real.log X)^C) :
    (fun X => angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) false)
      =o[atTop] firstMomentScale := by
  unfold angular_scaleFirstStoppedSum
  apply Asymptotics.IsLittleO.fun_sum
  intro i _hi
  obtain ⟨τ,K,hτ,hK,hbound⟩ := angular_distinguishedStoppedLate_bound ℓ i hpnt hC hξ
    hρ hρ₂ hε hsmall hgap Ct
  obtain ⟨D,hD,hagg⟩ := angular_distinguishedScaleStopped_bound ℓ i hρ
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => (1+Real.log X)^(i+5+Ct)*X^(5/6-τ)) ?_
    (log_power_powerSaving_isLittleO (i+5+Ct) hτ)
  apply Asymptotics.IsBigO.of_bound (D*K)
  filter_upwards [hbound,hH,hh,hboundary,eventually_ge_atTop (1:ℝ)]
    with X hbound hH hh hboundary hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hpiece (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ)
      (hq : q ∈ (if false then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h X) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)))
      (j r : ℕ) :
      ‖angular_distinguishedStoppedDyad ℓ i ρ ξ Ct (H X) X (h X) false d q j r‖ ≤
        K*(1+Real.log X)^Ct*X^(5/6-τ) := by
    have hk : 1 ≤ q.2.1 := (Finset.mem_filter.mp hq).2
    exact hbound (H X) hH (h X) hh hboundary d q j r hk
  have hs := hagg Ct ξ (H X) X hX (h X) false
    (K*(1+Real.log X)^Ct*X^(5/6-τ)) (by positivity) hpiece
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1+Real.log X)^(i+5+Ct)*X^(5/6-τ))]
  apply hs.trans_eq
  rw [pow_add]
  ring

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.angular_scaleFirstStoppedLate_isLittleO_oai := @OAI.CubicFirstMoment.angular_scaleFirstStoppedLate_isLittleO_oai
